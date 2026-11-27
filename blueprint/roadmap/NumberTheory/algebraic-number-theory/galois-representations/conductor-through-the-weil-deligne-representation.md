# Conductor of an ℓ-adic representation through its Weil–Deligne representation

Let $K$ be a finite extension of $\mathbb{Q}_p$, $\ell \ne p$ a prime, and $\rho \colon G_K \to \operatorname{GL}(V)$
a continuous representation on a finite-dimensional $\overline{\mathbb{Q}}_\ell$-vector space, with
[Weil–Deligne representation](weil-deligne-representations/weil-deligne-representation-of-an-l-adic-representation.md)
$\mathrm{WD}(V, \rho) = (V, r, N)$, defined through a lift $\varphi \in W_K$ of the geometric Frobenius and a
continuous surjective homomorphism $t \colon I_K \to \mathbb{Z}_\ell$ by
$\rho(\varphi^n \sigma) = r(\varphi^n \sigma) \exp(t(\sigma) N)$ for $n \in \mathbb{Z}$ and $\sigma \in I_K$. Let
$G_K^u$ be the ramification groups in the
[upper numbering](../discriminants-ramification/upper-numbering-of-ramification-groups.md) and $a(V, r, N)$
the [conductor of a Weil–Deligne representation](conductor-of-a-weil-deligne-representation.md). Then:

1. $\rho$ and $r$ agree on the wild inertia group $P_K$;
2. the vectors fixed by $\rho(I_K)$ are those of $\ker N$ fixed by $r(I_K)$: $V^{\rho(I_K)} = V_N^{I_K}$;
3. the conductor of $\rho$ is that of its Weil–Deligne representation:

    $$\int_{-1}^{\infty} \operatorname{codim} V^{\rho(G_K^u)} \, du = a(V, r, N).$$

The same holds for a representation on a vector space over a finite extension of $\mathbb{Q}_\ell$, after
extension of scalars to $\overline{\mathbb{Q}}_\ell$, which changes no codimension of a fixed subspace. In
particular, for an $\ell$-adic representation $\rho$ of $G_{\mathbb{Q}}$ and a prime $p \ne \ell$, the conductor
$m_p(\rho)$ of [Conductor of an ℓ-adic representation](conductor-of-an-l-adic-representation.md), whose
integrand differs from the one above only at $u = -1$, is the conductor of the Weil–Deligne representation of
$\rho|_{G_p}$, with $G_p \cong G_{\mathbb{Q}_p}$.

For item 1, $t$ vanishes on the pro-$p$ group $P_K$, whose continuous image in $\mathbb{Z}_\ell$ is trivial. For
item 2, a vector of $\ker N$ fixed by $r(I_K)$ is fixed by every $\rho(\sigma) = r(\sigma)\exp(t(\sigma)N)$,
$\sigma \in I_K$; conversely, $\ker r \cap I_K$ is open in $I_K$, so it contains a $\sigma_0$ with
$t(\sigma_0) \ne 0$, and a vector $v$ fixed by $\rho(I_K)$ satisfies $\exp(t(\sigma_0) N) v = v$, hence $N v = 0$
since $N$ is nilpotent, and then $r(\sigma) v = \rho(\sigma) v = v$ for every $\sigma \in I_K$. Item 3 follows:
for $-1 < u \le 0$ the integrand is $\operatorname{codim} V^{\rho(I_K)} = \operatorname{codim} V_N^{I_K}$, and for
$u > 0$ it is $\operatorname{codim} V^{r(G_K^u)}$ by item 1, as $G_K^u \subseteq P_K$.

## Depends on

- [Weil–Deligne representation of an ℓ-adic representation](weil-deligne-representations/weil-deligne-representation-of-an-l-adic-representation.md), for $\mathrm{WD}(V, \rho)$
- [Conductor of a Weil–Deligne representation](conductor-of-a-weil-deligne-representation.md), for $a(V, r, N)$
- [Upper numbering of ramification groups](../discriminants-ramification/upper-numbering-of-ramification-groups.md), for the groups $G_K^u$
- [Conductor of an ℓ-adic representation](conductor-of-an-l-adic-representation.md), for $m_p(\rho)$ in the global form

## Proof depends on

- [Weil–Deligne representation of an ℓ-adic representation](weil-deligne-representations/weil-deligne-representation-of-an-l-adic-representation.md), for the formula $\rho(\varphi^n \sigma) = r(\varphi^n \sigma) \exp(t(\sigma) N)$ and the openness of $\ker r$
- [Weil–Deligne representations](weil-deligne-representations/weil-deligne-representations.md), for the nilpotence of $N$
- [Inertia and tame inertia of a p-adic field](weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for $P_K$ being a pro-$p$ group
- [Upper numbering of ramification groups](../discriminants-ramification/upper-numbering-of-ramification-groups.md), for $G_K^u = I_K$ when $-1 < u \le 0$ and $G_K^u \subseteq P_K$ when $u > 0$

## Sources

- D. Ulmer, "Conductors of ℓ-adic representations", Proc. Amer. Math. Soc. 144 (2016), no. 6, 2291–2299,
  doi:10.1090/proc/12880, for $\ell$-adic representations of the Weil group $W_F$ with values in
  $\mathrm{GL}_n(E)$, $E$ a finite extension of $\mathbb{Q}_\ell$:
  - §8, p. 2296: the Weil–Deligne representation $(\rho, N)$ of $\rho_\ell$, "(8.1)
    $\rho_\ell(\Phi^m \sigma) = \rho(\Phi^m \sigma) \exp(t_\ell(\sigma) N)$", and $a_D(\rho_\ell) := a(\rho, N)$, after
    Deligne;
  - §8, p. 2297: "$t_\ell$ is trivial on the wild inertia group $P_F = G^{>0}_F$, so $\rho_\ell$ and $\rho$ are equal on
    $P_F$" and "equation (8.1) (with $m = 0$) implies that $V_N^{I_F} = V_\ell^{I_F}$", so that the definitions of
    Deligne and Serre agree;
  - §9, Theorem 1, p. 2297: "(9.1) $\int_{-1}^{\infty} \operatorname{codim} V_\ell^{G^s}\,ds = a(\rho_\ell) = a_D(\rho_\ell)$",
    with its proof, and footnote 1, p. 2291, on the formula appearing as a definition in Darmon–Diamond–Taylor,
    §2.1.
