# Chebotarev density theorem

Let $L/K$ be a finite Galois extension of number fields with Galois group $G$, and let $C \subseteq G$
be stable under conjugation. For a nonzero prime ideal $\mathfrak{p}$ of $\mathcal{O}_K$ unramified in
$L$, the Frobenius elements of the primes $\mathfrak{P}$ of $\mathcal{O}_L$ above $\mathfrak{p}$, the
elements $\sigma \in G$ with $\sigma(\mathfrak{P}) = \mathfrak{P}$ and
$\sigma(x) \equiv x^{N\mathfrak{p}} \pmod{\mathfrak{P}}$ for all $x \in \mathcal{O}_L$, form a
conjugacy class $\mathrm{Frob}_{\mathfrak{p}}$ of $G$. Then the set

$$T = \{\mathfrak{p} \text{ unramified in } L : \mathrm{Frob}_{\mathfrak{p}} \subseteq C\}$$

has Dirichlet density $|C| / |G|$:

$$\sum_{\mathfrak{p} \in T} N\mathfrak{p}^{-s} = \frac{|C|}{|G|} \log \frac{1}{s - 1} + o\Bigl(\log \frac{1}{s - 1}\Bigr) \qquad (s \to 1^+,\ s \text{ real}).$$

Because the set of all nonzero prime ideals has Dirichlet density $1$ (Milne,
Proposition VI.4.4(a)), this is equivalent to
$\sum_{\mathfrak{p} \in T} N\mathfrak{p}^{-s} / \sum_{\mathfrak{p}} N\mathfrak{p}^{-s} \to |C| / |G|$
as $s \to 1^+$, the sum in the denominator running over all nonzero prime ideals of $\mathcal{O}_K$.

Milne's proof first treats abelian extensions. By the reciprocity law, the Artin map identifies
$\mathrm{Gal}(L/K)$ with a quotient $I^{\mathfrak{m}} / H$ of a group of fractional ideals coprime to
a modulus $\mathfrak{m}$ by a subgroup $H$ containing the principal ideals $(a)$ with
$a \equiv 1 \bmod \mathfrak{m}$, and sends a prime to its Frobenius element; so it suffices that the
primes in each class of $I^{\mathfrak{m}} / H$ have Dirichlet density $1 / (I^{\mathfrak{m}} : H)$
(Corollary VIII.7.3). That equidistribution follows from $L(1, \chi) \neq 0$ for every nontrivial
character $\chi$ of $I^{\mathfrak{m}} / H$ (Theorems VIII.7.1, VIII.7.2 and VI.4.8), where the
$L$-functions extend holomorphically to a neighbourhood of $s = 1$. Through the isomorphism between
ray class groups and quotients of the idèle class group (Milne, Proposition V.4.6), these characters
are Hecke characters of finite order, and their $L$-functions differ from those of
[the continuation page](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md)
by finitely many Euler factors, which do not vanish at $s = 1$. For general $G$ and $C$ the class of
an element $\sigma$, the abelian case applied to $L$ over the fixed field of $\sigma$, restricted to
primes of degree one, gives the density $|C| / |G|$ (Theorem VIII.7.4).

## Proof depends on

- [Meromorphic continuation of Hecke L-functions](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-meromorphic-continuation.md)
- [Non-vanishing of Hecke L-functions on the line Re s = 1](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-nonvanishing-on-re-one.md)
- [Global Artin reciprocity](global-artin-reciprocity.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem VIII.7.4 (the statement, with Dirichlet
  density) and its proof through Theorems VIII.7.1 and VIII.7.2 and Corollary VIII.7.3; Section VI.4
  (definition of Dirichlet density, Proposition 4.4, Theorem 4.8); Theorem V.3.23 (the statement with
  $C$ a conjugacy class) and Theorem V.3.5 (Reciprocity Law, ideal-theoretic form).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: Theorem 28.9 (Chebotarev density
  theorem) and its proof; Lecture 22,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes22.pdf>, Corollary 22.22 ($L(1, \chi) \neq 0$
  for non-principal ray class characters, proved without class field theory).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>,
  no licence) uses this result, as `GroundTheory.Global.hasDirichletDensity_chebotarevSet`.
