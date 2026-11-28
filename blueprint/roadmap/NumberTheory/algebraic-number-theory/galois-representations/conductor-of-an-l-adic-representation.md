# Conductor of an ℓ-adic representation

Let $\ell$ be a prime and $K$ a finite extension of $\mathbb{Q}_\ell$. An **$\ell$-adic representation** of
$G_{\mathbb{Q}} = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ is a continuous homomorphism
$\rho \colon G_{\mathbb{Q}} \to \mathrm{GL}_d(K)$, for the profinite topology on $G_{\mathbb{Q}}$ and the
$\ell$-adic topology on $\mathrm{GL}_d(K)$, that is unramified at all but finitely many primes.

For a prime $p$, fix an extension $v_p$ of the $p$-adic valuation to $\overline{\mathbb{Q}}$ and let
$G_p \subseteq G_{\mathbb{Q}}$ be its stabilizer. It acts on the algebraic closure of $\mathbb{Q}_p$ in the
completion of $\overline{\mathbb{Q}}$ at $v_p$, and the resulting map $G_p \to G_{\mathbb{Q}_p}$ is an
isomorphism. Through it, let $I_p \subseteq G_p$ be the inertia group, $P_p \subseteq I_p$ the wild inertia
group, and, for $u \in [-1, \infty]$, $I_p^u \subseteq G_p$ the ramification group in the upper numbering
$G_{\mathbb{Q}_p}^u$ of [Upper numbering of ramification groups](../discriminants-ramification/ramification-groups-in-the-upper-numbering.md),
except that $I_p^{-1} = I_p$ and $I_p^\infty = 1$. So $I_p^u = I_p$ for $u \le 0$, and $I_p^u \subseteq P_p$ for
$u > 0$. The representation $\rho$ is **unramified at $p$** if $\rho(I_p) = 1$. For a subgroup
$H \subseteq G_{\mathbb{Q}}$, write $\rho^H$ for the subspace of $K^d$ fixed by every $\rho(\sigma)$,
$\sigma \in H$.

For a prime $p \neq \ell$, the **conductor of $\rho$ at $p$** is

$$m_p(\rho) = \int_{-1}^{\infty} \operatorname{codim} \rho^{I_p^u} \, du
= \operatorname{codim} \rho^{I_p} + \int_0^{\infty} \operatorname{codim} \rho^{I_p^u} \, du,$$

and the **conductor** of $\rho$ is

$$N(\rho) = \prod_{p \neq \ell} p^{m_p(\rho)}.$$

The integral is finite. The kernel $\Gamma$ of reduction
$\mathrm{GL}_d(\mathcal{O}_K) \to \mathrm{GL}_d(\mathcal{O}_K/\mathfrak{m}_K)$ is an open pro-$\ell$ subgroup of
$\mathrm{GL}_d(K)$, so $\rho^{-1}(\Gamma) \cap P_p$ is an open subgroup of the pro-$p$ group $P_p$, of finite index,
and its image in $\Gamma$ is trivial, a pro-$p$ group having no nontrivial continuous image in a pro-$\ell$ group
for $p \neq \ell$. Hence $\rho(P_p)$ is finite, and $\ker \rho \cap P_p = U \cap P_p$ for an open subgroup $U$ of
$G_p$. The groups $I_p^u$, $u > 0$, are closed, decreasing in $u$, contained in $P_p$, and have trivial
intersection; by compactness $I_p^u \subseteq U$ for some $u$, so $\rho$ is trivial on $I_p^u$ for all large $u$
and the integrand vanishes there. The value of $m_p(\rho)$ does not depend on the choice of $v_p$, since
another choice conjugates $G_p$, $I_p$ and the groups $I_p^u$ in $G_{\mathbb{Q}}$. If $\rho$ is unramified at
$p$, then $m_p(\rho) = 0$, so the product is finite.

## Depends on

- [Upper numbering of ramification groups](../discriminants-ramification/ramification-groups-in-the-upper-numbering.md), for the groups $G_{\mathbb{Q}_p}^u$
- [Inertia and tame inertia of a p-adic field](weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for the inertia group $I_p$ and the wild inertia group $P_p$

## Proof depends on

- [Inertia and tame inertia of a p-adic field](weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for $P_p$ being a pro-$p$ group, which makes $\rho(P_p)$ finite
- [Upper numbering of ramification groups](../discriminants-ramification/ramification-groups-in-the-upper-numbering.md), for the closed subgroups $G_{\mathbb{Q}_p}^u \subseteq P_p$ ($u > 0$), decreasing in $u$ with trivial intersection, so that $\rho(I_p^u) = 1$ for large $u$

## Sources

- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", in *Current Developments in Mathematics, 1995*,
  International Press, Cambridge, MA, 1995; page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>, §2.1:
  - pp. 50–51: $I_p$, the wild inertia group $P_p$, the groups $I_p^u$ with $I_p^{-1} = I_p$, and
    $G_p \cong G_{\mathbb{Q}_p}$;
  - p. 52: unramified representations; p. 53: "ℓ-adic representations, i.e. continuous representations
    $G_{\mathbb{Q}} \to \mathrm{GL}_d(K)$, where $K$ is a finite extension of $\mathbb{Q}_\ell$. We require that an
    ℓ-adic representation be unramified at all but finitely many primes", and $\rho^H$;
  - p. 54: the finiteness of $\rho(P_p)$ and the definitions of $m_p(\rho)$ and $N(\rho)$ ("If $p \ne \ell$ then
    we define the conductor, $m_p(\rho)$, of $\rho$ at $p$ by $m_p(\rho) = \int_{-1}^\infty \operatorname{codim}
    \rho^{I_p^u}\,du = \operatorname{codim} \rho^{I_p} + \int_0^\infty \operatorname{codim} \rho^{I_p^u}\,du$. This is
    well-defined as $\rho(P_p)$ is a finite group."). Darmon, Diamond and Taylor use the same local formula for
    mod $\ell$ representations and, at every prime, for Artin representations, but for an Artin representation
    the product $N(\rho)$ runs over all primes, $\ell$ included ("where the product is over all primes $p \ne \ell$
    in the case of an ℓ-adic or mod ℓ representation and over all primes in the case of an Artin
    representation").
