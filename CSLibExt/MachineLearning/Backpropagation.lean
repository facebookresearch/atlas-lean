/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import MathlibExt.Analysis.Calculus.Gradient

/-!
# Backpropagation computes the gradient of a feedforward network

Backpropagation (Rumelhart, Hinton and Williams, *Learning representations by back-propagating
errors*, Nature 323, 1986; Bishop, *Pattern Recognition and Machine Learning*, Section 5.3) for
feedforward networks with arbitrary differentiable layers between Euclidean spaces of widths
`d 0, d 1, …`. The forward pass applies the layers in order. The backward pass starts from the
loss gradient at the output and applies the adjoint of each layer's Jacobian at its forward
activation, from the last layer to the first (Bishop's `δ` recursion).

Main results:

* The chain rule for gradients, `∇ (f ∘ g) x = (Dg x)† ∇ f (g x)`, is
  `MetaMathlibExt.gradient_comp` (`MathlibExt/Analysis/Calculus/Gradient.lean`).
* `Net.DiffAlong`: the traversed layers are differentiable at their forward activations (only
  these are assumed); `Net.diffAlong_of_differentiable`.
* `Net.backward_eq`: **the backward pass is the vector-Jacobian product** `(D forward_n x)† δ`.
* `gradient_comp_forward`: **backpropagation computes the input gradient** of `ℓ ∘ forward_n`.
* `gradient_param`: for networks with parameters (`PNet`), **backpropagation computes the
  gradient with respect to each layer's parameters**: the adjoint of the layer's parameter
  derivative applied to the vector backpropagated to the layer's output (`Net.shift`,
  `Net.forward_add`).

## Cost model

None: the subject is derivatives over the reals. As written, `backward` recomputes each forward
activation; caching the activations, as implementations do, does not change the values.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Backpropagation

open InnerProductSpace ContinuousLinearMap
open MetaMathlibExt (gradient_comp)
open scoped Gradient

/-- **Feedforward network.** Given layer widths $d : \mathbb{N} \to \mathbb{N}$, a feedforward
network with widths $d$ is a sequence of arbitrary maps
$f_k : \mathbb{R}^{d(k)} \to \mathbb{R}^{d(k+1)}$, one for each $k \in \mathbb{N}$, where $f_k$ is
the map computed by layer $k$ and $\mathbb{R}^n$ carries its Euclidean structure. -/
structure Net (d : ℕ → ℕ) where
  /-- The map computed by layer `k`. -/
  layer : (k : ℕ) → EuclideanSpace ℝ (Fin (d k)) → EuclideanSpace ℝ (Fin (d (k + 1)))

variable {d : ℕ → ℕ} (N : Net d)

/-- **The forward pass.** For a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, the forward pass
through the first $n$ layers is the map $N_n : \mathbb{R}^{d_0} \to \mathbb{R}^{d_n}$ given by
$N_0(x) = x$ and $N_{n+1}(x) = f_n(N_n(x))$, that is, $N_n = f_{n-1} \circ \cdots \circ f_0$. -/
def Net.forward : (n : ℕ) → EuclideanSpace ℝ (Fin (d 0)) → EuclideanSpace ℝ (Fin (d n))
  | 0, x => x
  | n + 1, x => N.layer n (forward n x)

/-- **The backward pass.** Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ be an input, and write $a_k \in \mathbb{R}^{d_k}$ for the forward pass of
$x$ through the first $k$ layers. For each $n \in \mathbb{N}$, the backward pass at $x$ sends a
vector $\delta \in \mathbb{R}^{d_n}$ to $B_n(\delta) \in \mathbb{R}^{d_0}$, defined by
$B_0(\delta) = \delta$ and $B_{n+1}(\delta) = B_n(Df_n(a_n)^* \, \delta)$, where $Df_n(a_n)$ is the
Fréchet derivative of $f_n$ at $a_n$ (taken to be $0$ if $f_n$ is not differentiable there) and
$^*$ denotes the adjoint. Thus
$B_n(\delta) = Df_0(a_0)^* \cdots Df_{n-1}(a_{n-1})^* \, \delta$: the adjoints of the layer
Jacobians are applied from the last layer to the first. -/
noncomputable def Net.backward (x : EuclideanSpace ℝ (Fin (d 0))) :
    (n : ℕ) → EuclideanSpace ℝ (Fin (d n)) → EuclideanSpace ℝ (Fin (d 0))
  | 0, δ => δ
  | n + 1, δ => backward x n (adjoint (fderiv ℝ (N.layer n) (N.forward n x)) δ)

/-- **Differentiability along the forward pass.** Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write $a_j \in \mathbb{R}^{d_j}$ for the
forward pass of $x$ through the first $j$ layers. The network is differentiable along the forward
pass of $x$ through its first $n$ layers when $f_j$ is differentiable at $a_j$ for every
$j < n$. -/
def Net.DiffAlong (x : EuclideanSpace ℝ (Fin (d 0))) (n : ℕ) : Prop :=
  ∀ j < n, DifferentiableAt ℝ (N.layer j) (N.forward j x)

/-- **Differentiable layers are differentiable along every forward pass.** Let $N$ be a
feedforward network with layers $f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between
Euclidean spaces. If every $f_k$ is differentiable on all of $\mathbb{R}^{d_k}$, then for every
input $x \in \mathbb{R}^{d_0}$ and every $n \in \mathbb{N}$, the layer $f_j$ is differentiable at
the forward pass of $x$ through the first $j$ layers for every $j < n$. -/
theorem Net.diffAlong_of_differentiable (hN : ∀ k, Differentiable ℝ (N.layer k))
    (x : EuclideanSpace ℝ (Fin (d 0))) (n : ℕ) : N.DiffAlong x n :=
  fun j _ => (hN j).differentiableAt

/-- **Differentiability of the forward pass.** Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write
$N_j : \mathbb{R}^{d_0} \to \mathbb{R}^{d_j}$ for the forward pass through the first $j$ layers. If
$f_j$ is differentiable at $N_j(x)$ for every $j < n$, then $N_n$ is differentiable at $x$. -/
theorem Net.differentiableAt_forward (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ n, N.DiffAlong x n → DifferentiableAt ℝ (N.forward n) x
  | 0, _ => differentiableAt_id
  | n + 1, hN => (hN n (by omega)).comp x
      (differentiableAt_forward x n fun j hj => hN j (by omega))

/-- **The backward pass is the vector-Jacobian product.** Let $N$ be a feedforward network with
layers $f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write
$N_j : \mathbb{R}^{d_0} \to \mathbb{R}^{d_j}$ for the forward pass through the first $j$ layers. If
$f_j$ is differentiable at $N_j(x)$ for every $j < n$, then for every $\delta \in \mathbb{R}^{d_n}$
the backward pass from $\delta$ at input $x$ through the first $n$ layers equals
$DN_n(x)^* \, \delta$, where $DN_n(x)$ is the Fréchet derivative of $N_n$ at $x$ and $^*$ denotes
the adjoint. -/
theorem Net.backward_eq (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ (n : ℕ), N.DiffAlong x n → ∀ δ : EuclideanSpace ℝ (Fin (d n)),
      N.backward x n δ = adjoint (fderiv ℝ (N.forward n) x) δ
  | 0, _, δ => by
      simp only [backward]
      rw [show N.forward 0 = id from rfl, fderiv_id, adjoint_id, id_apply]
  | n + 1, hN, δ => by
      have hN' : N.DiffAlong x n := fun j hj => hN j (by omega)
      have hcomp : N.forward (n + 1) = N.layer n ∘ N.forward n := rfl
      rw [backward, backward_eq x n hN', hcomp,
        fderiv_comp x (hN n (by omega)) (N.differentiableAt_forward x n hN'), adjoint_comp,
        comp_apply]

/-- **Backpropagation computes the input gradient.** Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, let
$x \in \mathbb{R}^{d_0}$ and $n \in \mathbb{N}$, and write $N_j$ for the forward pass through the
first $j$ layers. Assume that $f_j$ is differentiable at $N_j(x)$ for every $j < n$, and let
$\ell : \mathbb{R}^{d_n} \to \mathbb{R}$ be differentiable at $N_n(x)$. Then
$\nabla(\ell \circ N_n)(x)$ is the backward pass of $\nabla \ell(N_n(x))$ at input $x$ through
the first $n$ layers, that is,
$\nabla(\ell \circ N_n)(x) = Df_0(N_0(x))^* \cdots Df_{n-1}(N_{n-1}(x))^* \, \nabla \ell(N_n(x))$,
where $Df_j(N_j(x))$ is the Fréchet derivative of $f_j$ at $N_j(x)$ and $^*$ denotes the
adjoint. -/
theorem gradient_comp_forward {n : ℕ} (ℓ : EuclideanSpace ℝ (Fin (d n)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (d 0))) (hN : N.DiffAlong x n)
    (hℓ : DifferentiableAt ℝ ℓ (N.forward n x)) :
    ∇ (ℓ ∘ N.forward n) x = N.backward x n (∇ ℓ (N.forward n x)) := by
  rw [N.backward_eq x n hN, gradient_comp hℓ (N.differentiableAt_forward x n hN)]

/-! ## Parameter gradients -/

/-- **Shifted network.** For a feedforward network $N$ with layer widths $d$ and a natural number
$j$, the shifted network has layer widths $i \mapsto d(j + i)$, and its layer $i$ is layer
$j + i$ of $N$. It is made of the layers of $N$ from layer $j$ on. -/
def Net.shift (j : ℕ) : Net (fun i => d (j + i)) := ⟨fun i => N.layer (j + i)⟩

/-- **Splitting the forward pass.** Let $N$ be a feedforward network with layers
$f_k : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ between Euclidean spaces, write $N_n$ for its
forward pass through the first $n$ layers, and for $j \in \mathbb{N}$ write $N^{(j)}_m$ for the
forward pass through the first $m$ layers of the shifted network with layers
$f_j, f_{j+1}, \dots$. Then for all $j, m \in \mathbb{N}$ and $x \in \mathbb{R}^{d_0}$,
$N_{j+m}(x) = N^{(j)}_m(N_j(x))$. -/
theorem Net.forward_add (j : ℕ) (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ m, N.forward (j + m) x = (N.shift j).forward m (N.forward j x)
  | 0 => rfl
  | m + 1 => by
      change N.layer (j + m) (N.forward (j + m) x) = _
      rw [forward_add j x m]
      rfl

/-- **Parametrized feedforward network.** Given layer widths $d : \mathbb{N} \to \mathbb{N}$ and
parameter dimensions $p : \mathbb{N} \to \mathbb{N}$, a parametrized network is a sequence of
arbitrary maps $f_k : \mathbb{R}^{p(k)} \times \mathbb{R}^{d(k)} \to \mathbb{R}^{d(k+1)}$, one for
each $k \in \mathbb{N}$: layer $k$ sends parameters $\theta \in \mathbb{R}^{p(k)}$ and an input
$x \in \mathbb{R}^{d(k)}$ to $f_k(\theta, x)$. -/
structure PNet (d p : ℕ → ℕ) where
  /-- The map computed by layer `k` with parameters `θ`. -/
  layer : (k : ℕ) → EuclideanSpace ℝ (Fin (p k)) → EuclideanSpace ℝ (Fin (d k)) →
    EuclideanSpace ℝ (Fin (d (k + 1)))

variable {p : ℕ → ℕ}

/-- **The network at fixed parameters.** Let $P$ be a network with parameters whose layer $k$ is a
map $g_k : \mathbb{R}^{p_k} \times \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$ of the parameters
and the input (all spaces Euclidean). For parameters $\theta = (\theta_k)_{k \in \mathbb{N}}$ with
$\theta_k \in \mathbb{R}^{p_k}$, the network at $\theta$ is the feedforward network whose layer
$k$ is $g_k(\theta_k, \cdot) : \mathbb{R}^{d_k} \to \mathbb{R}^{d_{k+1}}$. -/
def PNet.net (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k))) : Net d :=
  ⟨fun k => P.layer k (θ k)⟩

theorem PNet.forward_update_of_le (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k)))
    (k : ℕ) (t : EuclideanSpace ℝ (Fin (p k))) (x : EuclideanSpace ℝ (Fin (d 0))) :
    ∀ j, j ≤ k → (P.net (Function.update θ k t)).forward j x = (P.net θ).forward j x
  | 0, _ => rfl
  | j + 1, hj => by
      change P.layer j (Function.update θ k t j) _ = P.layer j (θ j) _
      rw [Function.update_of_ne (by omega), forward_update_of_le P θ k t x j (by omega)]

theorem PNet.shift_update (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k))) (k : ℕ)
    (t : EuclideanSpace ℝ (Fin (p k))) :
    (P.net (Function.update θ k t)).shift (k + 1) = (P.net θ).shift (k + 1) := by
  simp only [Net.shift, PNet.net]
  congr 1
  funext i
  rw [Function.update_of_ne (by omega)]

/-- **Backpropagation computes the parameter gradients.** Let $P$ be a network with parameters
whose layer $i$ is a map $g_i : \mathbb{R}^{p_i} \times \mathbb{R}^{d_i} \to \mathbb{R}^{d_{i+1}}$
of the parameters and the input (all spaces Euclidean). Fix parameters $\theta = (\theta_i)_i$
with $\theta_i \in \mathbb{R}^{p_i}$, let $N$ be the network with layers
$f_i = g_i(\theta_i, \cdot)$, let $x \in \mathbb{R}^{d_0}$ and $k, m \in \mathbb{N}$, set
$L = k + 1 + m$, and write $a_j$ for the forward pass of $x$ through the first $j$ layers of $N$.
Assume that $f_{k+1+i}$ is differentiable at $a_{k+1+i}$ for every $i < m$, that
$h(t) = g_k(t, a_k)$ is differentiable at $\theta_k$, and that
$\ell : \mathbb{R}^{d_L} \to \mathbb{R}$ is differentiable at $a_L$. For
$t \in \mathbb{R}^{p_k}$ let $\Phi(t)$ be the forward pass of $x$ through the first $L$ layers of
the network obtained by replacing $\theta_k$ with $t$. Then
$$\nabla(\ell \circ \Phi)(\theta_k) = Dh(\theta_k)^* \, \delta,$$
where $\delta = Df_{k+1}(a_{k+1})^* \cdots Df_{L-1}(a_{L-1})^* \, \nabla \ell(a_L)$ (so
$\delta = \nabla \ell(a_L)$ when $m = 0$) is the backward pass of $\nabla \ell(a_L)$ through
layers $k + 1, \dots, L - 1$ of $N$, $D$ denotes the Fréchet derivative and $^*$ the adjoint. -/
theorem gradient_param (P : PNet d p) (θ : (k : ℕ) → EuclideanSpace ℝ (Fin (p k)))
    (x : EuclideanSpace ℝ (Fin (d 0))) (k m : ℕ)
    (hN : ∀ i < m, DifferentiableAt ℝ ((P.net θ).layer (k + 1 + i))
      ((P.net θ).forward (k + 1 + i) x))
    (hk : DifferentiableAt ℝ (fun t => P.layer k t ((P.net θ).forward k x)) (θ k))
    (ℓ : EuclideanSpace ℝ (Fin (d (k + 1 + m))) → ℝ)
    (hℓ : DifferentiableAt ℝ ℓ ((P.net θ).forward (k + 1 + m) x)) :
    ∇ (fun t => ℓ ((P.net (Function.update θ k t)).forward (k + 1 + m) x)) (θ k) =
      adjoint (fderiv ℝ (fun t => P.layer k t ((P.net θ).forward k x)) (θ k))
        (((P.net θ).shift (k + 1)).backward ((P.net θ).forward (k + 1) x) m
          (∇ ℓ ((P.net θ).forward (k + 1 + m) x))) := by
  set S := (P.net θ).shift (k + 1)
  set g := fun t => P.layer k t ((P.net θ).forward k x)
  have hfun : (fun t => ℓ ((P.net (Function.update θ k t)).forward (k + 1 + m) x)) =
      (ℓ ∘ S.forward m) ∘ g := by
    funext t
    rw [Net.forward_add, PNet.shift_update]
    change ℓ (S.forward m (P.layer k (Function.update θ k t k) _)) = _
    rw [Function.update_self, PNet.forward_update_of_le P θ k t x k le_rfl]
    rfl
  have hS : S.DiffAlong ((P.net θ).forward (k + 1) x) m := fun i hi => by
    change DifferentiableAt ℝ ((P.net θ).layer (k + 1 + i)) _
    rw [← Net.forward_add]
    exact hN i hi
  have hg : g (θ k) = (P.net θ).forward (k + 1) x := rfl
  have hout : S.forward m ((P.net θ).forward (k + 1) x) = (P.net θ).forward (k + 1 + m) x :=
    (Net.forward_add (P.net θ) (k + 1) x m).symm
  have hℓ' : DifferentiableAt ℝ ℓ (S.forward m ((P.net θ).forward (k + 1) x)) := by
    rw [hout]; exact hℓ
  rw [hfun, gradient_comp (f := ℓ ∘ S.forward m) (g := g)
      (by exact hℓ'.comp _ (S.differentiableAt_forward _ m hS)) hk, hg,
    gradient_comp_forward S ℓ _ hS hℓ', hout]

end Cslib.MachineLearning.Backpropagation
