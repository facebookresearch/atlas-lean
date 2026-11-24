# Galois invariants of the idèle class group

Let $L/K$ be a finite Galois extension of number fields with Galois group $G$, let
$C_L = \mathbb{I}_L / L^\times$ and $C_K = \mathbb{I}_K / K^\times$ be the idèle class groups, and let $G$ act
on $C_L$ through its action on the idèles ($\sigma a$ has component $\sigma(a_w)$ at $\sigma w$). Then:

1. The homomorphism $C_K \to C_L$ induced by the embedding $\mathbb{I}_K \to \mathbb{I}_L$ (which puts
   $a_v$ at every place above $v$) is injective, with image the invariants $C_L^G$.
2. The idèle norm $\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$,
   $\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$, restricts to the field norm on
   $L^\times$, so it induces a norm map $\mathrm{Nm}_{L/K} \colon C_L \to C_K$, which under part 1 is
   the group norm $N_G \colon x \mapsto \prod_{\sigma \in G} \sigma x$. Hence

    $$\hat H^0(G, C_L) = C_L^G / N_G(C_L) \cong C_K / \mathrm{Nm}_{L/K}(C_L).$$


3. The quotient map $\mathbb{I}_K \to C_K$ induces an isomorphism

    $$\mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L) \cong C_K / \mathrm{Nm}_{L/K}(C_L).$$

Part 1 comes from the cohomology sequence of $1 \to L^\times \to \mathbb{I}_L \to C_L \to 1$: the
invariants of $L^\times$ and of $\mathbb{I}_L$ are $K^\times$ and the image of $\mathbb{I}_K$, and
$H^1(G, L^\times) = 0$ by [Hilbert's Theorem 90](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md) for the finite Galois extension $L/K$
(Milne, Proposition II.1.22). Part 3 follows from the snake lemma applied to the
norm maps between the sequences $1 \to L^\times \to \mathbb{I}_L \to C_L \to 1$ and
$1 \to K^\times \to \mathbb{I}_K \to C_K \to 1$.

## Depends on

- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for $H^1(G, L^\times) = 0$ in part 1
- [Cohomology of the idèle group of a Galois extension](cohomology-of-the-idele-group.md), for the invariants $\mathbb{I}_L^G = \mathbb{I}_K$ (its part 1)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Lemma VII.4.1 (part 1) and its proof, with
  Proposition II.1.22 (Hilbert's Theorem 90); Section VII.2,
  "The norm map on idèles" (the norm $x \mapsto \prod_\sigma \sigma x$ on $\mathbb{I}_L$, the induced norm
  on $C_L$ and part 3); the first line of the proof of Lemma VII.5.2
  ($\mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L) \cong C_K / \mathrm{Nm}_{L/K}(C_L) = \hat H^0_T(G, C_L)$).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: Definition 28.1 (the idèle norm)
  and the induced norm on idèle class groups.
