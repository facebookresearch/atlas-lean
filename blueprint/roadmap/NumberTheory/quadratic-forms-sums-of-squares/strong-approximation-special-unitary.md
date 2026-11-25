# Strong approximation for special unitary groups

Let $K$ be a number field with ring of integers $\mathfrak{o}$, $E/K$ a quadratic field extension with
ring of integers $\mathcal{O}$, and $(V, \Phi)$ a regular
[Hermitian space](hermitian-local-global-principle.md) over $E$ of rank $m \ge 2$. Let
$\mathrm{SU}(V, \Phi)$ be the group of $E$-linear isometries of $(V, \Phi)$ of determinant $1$, and for
a prime ideal $\mathfrak{p}$ of $\mathfrak{o}$ let $\mathrm{SU}(V_{\mathfrak{p}}, \Phi)$ be the
corresponding group of the completion $V_{\mathfrak{p}} = V \otimes_K K_{\mathfrak{p}}$. Let $S$ be a set
of prime ideals of $\mathfrak{o}$ and $T \subseteq S$ a finite subset, and suppose that there is a place
$v$ of $K$, not corresponding to an ideal in $S$, at which $(V_v, \Phi)$ is isotropic. Let $L$ be an
$\mathcal{O}$-lattice in $V$ and, for each $\mathfrak{p} \in T$, let
$\sigma_{\mathfrak{p}} \in \mathrm{SU}(V_{\mathfrak{p}}, \Phi)$. Then for every $k \ge 1$ there is
$\sigma \in \mathrm{SU}(V, \Phi)$ such that

$$(\sigma - \sigma_{\mathfrak{p}})(L_{\mathfrak{p}}) \subseteq \mathfrak{p}^k L_{\mathfrak{p}} \quad (\mathfrak{p} \in T), \qquad \sigma(L_{\mathfrak{p}}) = L_{\mathfrak{p}} \quad (\mathfrak{p} \in S \setminus T).$$

So the global group $\mathrm{SU}(V, \Phi)$ approximates any finite family of local elements as closely
as wanted, while preserving the lattice at the other primes of $S$, provided the group is allowed to be
arbitrary at one place $v$ where the space is isotropic. Kirschmer states the theorem for
$\dim_K V \ge 3$; here $\dim_K V = 2m \ge 4$. At a real place $v$ of $K$ with
$E_v \cong \mathbb{C}$, isotropy of $V_v$ means that $V_v$ is indefinite, the condition for the group
$\mathrm{SU}(V_v, \Phi) \cong \mathrm{SU}(p, q)$ to be non-compact. A consequence is that, in an
indefinite space of rank at least $2$, the special genus of a lattice consists of a single isometry class
(Kirschmer, Corollary 5.1.4).

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>,
  Section 5.1: Definition 5.1.2 (special unitary group), Theorem 5.1.3 (Strong approximation), whose
  proof Kirschmer refers to M. Kneser, *Strong approximation*, in *Algebraic Groups and Discontinuous
  Subgroups* (Proc. Sympos. Pure Math., Boulder, 1965), Amer. Math. Soc. (1966), 187–196, and
  Corollary 5.1.4.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses an adelic form of this result, for CM extensions and a finite set $S$ of places such
  that the product over $S$ of the local special unitary groups is non-compact (it suffices that one
  factor is non-compact), as `GlobalTheory.Published.StrongApproxSU`.
