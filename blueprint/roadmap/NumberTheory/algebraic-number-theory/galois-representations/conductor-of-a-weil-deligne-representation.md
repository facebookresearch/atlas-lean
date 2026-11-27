# Conductor of a Weil–Deligne representation

Let $K$ be a finite extension of $\mathbb{Q}_p$ with Weil group $W_K$, inertia group $I_K$, wild inertia group
$P_K$ and ramification groups $G_K^u \subseteq G_K$ ($u \ge -1$) in the
[upper numbering](../discriminants-ramification/ramification-groups-in-the-upper-numbering.md), so that
$G_K^u = I_K$ for $-1 < u \le 0$ and $G_K^u \subseteq P_K$ for $u > 0$. Let $\Omega$ be an algebraically closed
field of characteristic $0$ and $r \colon W_K \to \operatorname{GL}(V)$ a homomorphism on a finite-dimensional
$\Omega$-vector space whose kernel is open, so that $r(I_K)$ is finite. For a subgroup $H$ of $W_K$ write $V^H$ for
the vectors fixed by $r(H)$. The **Artin conductor** of $r$ is

$$a(r) = \int_{-1}^{\infty} \operatorname{codim} V^{G_K^u} \, du
= \operatorname{codim} V^{I_K} + \operatorname{sw}(r), \qquad
\operatorname{sw}(r) = \int_{0}^{\infty} \operatorname{codim} V^{G_K^u} \, du,$$

the integrand being read for $u > -1$, where $G_K^u \subseteq I_K \subseteq W_K$; $\operatorname{sw}(r)$ is the
**Swan conductor** of $r$. The integrals are finite: $\ker r \cap I_K$ is open in $I_K$, and the closed
subgroups $G_K^u$, $u > 0$, decrease with trivial intersection, so $r$ is trivial on $G_K^u$ for all large $u$.
For a representation that factors through the group of a finite Galois extension $L/K$, $a(r)$ is Artin's sum
$\sum_{i \ge 0} \operatorname{codim} V^{G_i} / (G_0 : G_i)$ over the lower-numbering ramification groups $G_i$ of
$L/K$.

For a [Weil–Deligne representation](weil-deligne-representations/weil-deligne-representations.md)
$(V, r, N)$ of $W_K$ over $\Omega$, let $V_N = \ker N$ and
$V_N^{I_K} = \{ v \in V : N v = 0 \text{ and } r(\sigma) v = v \text{ for all } \sigma \in I_K \}$. The
**conductor** of $(V, r, N)$ is

$$a(V, r, N) = a(r) + \dim V^{I_K} - \dim V_N^{I_K} = \operatorname{codim} V_N^{I_K} + \operatorname{sw}(r).$$

It is a nonnegative real number that depends only on the isomorphism class of $(V, r, N)$, indeed only on
$r|_{I_K}$ and $N$, equals $a(r)$ when $N = 0$, and does not change under extension of scalars along a field
embedding $\Omega \to \Omega'$, since the fixed subspaces and kernels involved commute with it.

## Depends on

- [Weil–Deligne representations](weil-deligne-representations/weil-deligne-representations.md), for Weil–Deligne representations $(V, r, N)$
- [Weil group of a p-adic field](weil-deligne-representations/weil-group-of-a-p-adic-field.md), for $W_K$ and $I_K \subseteq W_K$
- [Upper numbering of ramification groups](../discriminants-ramification/ramification-groups-in-the-upper-numbering.md), for the groups $G_K^u$
- [Ramification groups of local fields](../discriminants-ramification/ramification-groups-of-local-fields.md), for the lower-numbering groups $G_i$ of a finite Galois extension $L/K$ in Artin's sum
- [Inertia and tame inertia of a p-adic field](weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for the wild inertia group $P_K$

## Proof depends on

- [Upper numbering of ramification groups](../discriminants-ramification/ramification-groups-in-the-upper-numbering.md), for $G_K^u = I_K$ when $-1 < u \le 0$, for $G_K^u \subseteq P_K$ when $u > 0$, and for the $G_K^u$ being closed, decreasing, with trivial intersection, which makes the integrals finite
- [Herbrand's functions](../discriminants-ramification/upper-numbering-of-ramification-groups-results/herbrand-functions.md), for the derivative $1/(G_0 : G_t)$ of $\varphi_{L/K}$ at non-integers, through which the substitution $u = \varphi_{L/K}(t)$ turns the integral into Artin's sum

## Sources

- D. Ulmer, "Conductors of ℓ-adic representations", Proc. Amer. Math. Soc. 144 (2016), no. 6, 2291–2299,
  doi:10.1090/proc/12880, for $F$ a finite extension of $\mathbb{Q}_p$ or of $\mathbb{F}_p((t))$:
  - §3, pp. 2292–2293 (the upper numbering on $G_F$, with $G_F^{-1} = G_F$ and $G_F^0 = I_F$);
  - §4, p. 2293: Artin's definition "(4.1) $a(\rho) := \sum_{i=0}^{\infty} \frac{\operatorname{codim} V^{G_i}}{[G_0 : G_i]}$",
    "Because the definition of $a(\rho)$ depends only on $\rho$ restricted to inertia, we may extend it to
    representations $\rho$ which are only assumed to have finite image after restriction to inertia", and the
    two integral expressions, the second being $a(\rho) = \int_{-1}^{\infty} \operatorname{codim} V^{G^s}\,ds$;
  - §4, p. 2294: $\epsilon(\rho) = \operatorname{codim} V^{I_F}$ and $\delta(\rho) = \int_0^\infty \operatorname{codim} V^{G^s}\,ds$, with
    $a(\rho) = \epsilon(\rho) + \delta(\rho)$ ("One calls $\epsilon(\rho)$ the tame conductor of $\rho$ and $\delta(\rho)$ the
    wild conductor or Swan conductor of $\rho$");
  - §7, p. 2296: Weil–Deligne representations $(\rho, N)$ with $\rho(w) N \rho(w)^{-1} = \lVert w \rVert N$, $\lVert \cdot \rVert$
    sending a geometric Frobenius to $q^{-1}$, and "We define the Artin conductor of a Weil-Deligne representation
    $(\rho, N)$ as $a(\rho, N) := a(\rho) + \dim V^{I_F} - \dim V_N^{I_F}$".
