# Mumford's construction of degenerating abelian varieties

Let $A$ be an excellent integrally closed noetherian ring with fraction field $K$, and $I \subset A$ an
ideal with $\sqrt{I} = I$ such that $A$ is complete for the $I$-adic topology; let
$S = \operatorname{Spec} A$, $\eta$ its generic point and $S_0 = \operatorname{Spec}(A/I)$. A smooth
commutative group scheme of finite type over a scheme $Z$ is **semi-abelian** if every fibre is
connected and is an extension of an abelian variety by a torus.

Let $\tilde G$ be a split torus of rank $r$ over $S$, with character group $X$ and characters
$\mathcal{X}^\alpha \in \Gamma(\tilde G, \mathcal{O}_{\tilde G})$ for $\alpha \in X$, so that
$\tilde G(K) \cong (K^*)^r$. A **set of periods** is a subgroup $Y \subset \tilde G(K)$ isomorphic to
$\mathbb{Z}^r$, and a **polarization** of $Y$ is a homomorphism $\phi \colon Y \to X$ such that
$\mathcal{X}^{\phi(y)}(z) = \mathcal{X}^{\phi(z)}(y)$ for all $y, z \in Y$ and
$\mathcal{X}^{\phi(y)}(y) \in I$ for all $y \ne 0$.

**Theorem** (Mumford). Let $Y \subset \tilde G(K)$ be a set of periods that admits a polarization.
There is a scheme $G$ over $S$, depending only on $\tilde G$ and $Y$, such that:

1. $G$ is a semi-abelian group scheme over $S$;
2. its generic fibre $G_\eta$ is an abelian variety over $K$;
3. the $I$-adic completions of $G$ and of $\tilde G$ are canonically isomorphic; in particular
   $G \times_S S_0 \cong \tilde G \times_S S_0$ is a split torus over $S_0$.

Mumford builds a relatively complete model $\tilde P$ of $\tilde G$ with respect to $Y$ and a
multiple $n\phi$ of the polarization (Theorem 2.5), divides it by $Y$ over each $A/I^n$ to obtain
projective schemes $P_n$ with ample sheaves (Theorem 3.10), algebraizes the resulting formal scheme
with [Grothendieck's existence theorem](grothendieck-existence-theorem.md) to a scheme $P$ projective
over $S$, and takes for $G$ an open subscheme of $P$ whose completion is that of $\tilde G$. He then
shows that $G$ is smooth over $S$ (Corollary 4.2), that it depends only on $\tilde G$ and $Y$ and not on
the polarization or the model (Corollary 4.7), that it is a group scheme (Corollary 4.8) with abelian
generic fibre (Corollary 4.9), and that its fibres are connected, so that $G$ is semi-abelian
(Corollary 4.12). He also shows that $Y$ is determined by $G$: if $\tilde G / Y_1 \cong \tilde G / Y_2$
then $Y_1 = Y_2$; whether every semi-abelian $G$ as above arises in this way is not discussed there.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties

## Proof depends on

- [Grothendieck's existence theorem](grothendieck-existence-theorem.md), for the algebraization of a
  proper formal scheme with an ample invertible sheaf (item 3)

## Sources

- D. Mumford, "An analytic construction of degenerating abelian varieties over complete rings",
  Compositio Math. 24 (1972), 239–272, <http://www.numdam.org/item?id=CM_1972__24_3_239_0>: the
  introduction (the standing hypotheses on $A$ and $I$, semi-abelian group schemes, the plan of the
  construction), Definitions 1.1 and 1.2 (periods and polarizations), Definition 2.1 and Theorem 2.5
  (relatively complete models), Theorem 3.10 and the construction of $G$ that follows it (citing EGA
  III, (5.4.5)), Corollaries 4.2, 4.7, 4.8, 4.9 and 4.12.
- G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Ergebnisse der Mathematik (3) 22,
  Springer, 1990: the chapter "Mumford's Construction" (pp. 53–92).
