# Modular forms of type (k, ε) on Γ₀(N)

Let $N \ge 1$ and $k$ be integers. For a function $f$ on the upper half-plane
$\mathfrak{H} = \{z \in \mathbb{C} : \operatorname{Im}(z) > 0\}$ and
$\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{SL}_2(\mathbb{R})$, write
$(f|_k\gamma)(z) = (cz + d)^{-k} f(\gamma z)$, where $\gamma z = (az + b)/(cz + d)$. A modular form of weight $k$ on
[$\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/congruence-subgroup-gamma1.md) is a holomorphic function
$f$ on $\mathfrak{H}$ with $f|_k\gamma = f$ for every $\gamma \in \Gamma_1(N)$ and that is holomorphic at the cusps:
for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $f|_k\sigma$ has an expansion in powers of $e^{2\pi i z/N}$
with exponents $\ge 0$. It is a cusp form if, for every $\sigma$, these exponents are all $> 0$, that is, if $f$ is a
[cusp form](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/cusp-form.md) of weight $k$ for $\Gamma_1(N)$. Since
$\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix} \in \Gamma_1(N)$, such an $f$ satisfies $f(z + 1) = f(z)$, and its
$q$-expansion is its expansion $f = \sum_{n \ge 0} c_n q^n$ in powers of $q = e^{2\pi i z}$.

Let $\varepsilon$ be a Dirichlet character mod $N$, that is, a homomorphism
$\varepsilon \colon (\mathbb{Z}/N\mathbb{Z})^* \to \mathbb{C}^*$, with $\varepsilon(-1) = (-1)^k$. A modular form of
type $(k, \varepsilon)$ on $\Gamma_0(N)$ is a modular form $f$ of weight $k$ on $\Gamma_1(N)$ such that

$$f\left(\frac{az+b}{cz+d}\right) = \varepsilon(d)\,(cz+d)^k f(z) \qquad \text{for all } \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(N),$$

where [$\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/congruence-subgroup-gamma0.md) is the group of the
matrices of $\mathrm{SL}_2(\mathbb{Z})$ with $c \equiv 0 \pmod N$ and $\varepsilon(d)$ is the value of $\varepsilon$ at
the class of $d$, which is prime to $N$. A cusp form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ is a modular form of
type $(k, \varepsilon)$ on $\Gamma_0(N)$ that is a cusp form. Without the condition $\varepsilon(-1) = (-1)^k$ the
transformation law for $-1 \in \Gamma_0(N)$, $f = \varepsilon(-1)(-1)^k f$, would force $f = 0$.

For a prime $p \nmid N$, the Hecke operator $T_p$ sends a modular form $f = \sum_{n \ge 0} c_n q^n$ of type
$(k, \varepsilon)$ on $\Gamma_0(N)$ to the series

$$f|T_p = \sum_{n \ge 0} c_{pn} q^n + \varepsilon(p)\, p^{k-1} \sum_{n \ge 0} c_n q^{pn}.$$

For $f \ne 0$, $f$ is an eigenvector of $T_p$ with eigenvalue $a_p \in \mathbb{C}$ if $f|T_p = a_p f$, that is, if
$c_{pn} + \varepsilon(p)\, p^{k-1} c_{n/p} = a_p c_n$ for every $n \ge 0$, where $c_{n/p} = 0$ when $p \nmid n$. For
$f \ne 0$, $f$ is an eigenvector of the $T_p$, $p \nmid N$, with eigenvalues $a_p$ if $f|T_p = a_p f$ for every prime
$p \nmid N$. As for an [eigenvector of a linear map](../../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/has-eigenvector.md), an eigenvector is nonzero: the
zero form satisfies $0|T_p = a \cdot 0$ for every $a \in \mathbb{C}$.

These are the definitions of §§1.1–1.6 of Deligne–Serre, with $T_p$ given by their formula (1.6.1); the eigenvectors of
their Théorème 4.1 and Proposition 5.1 are forms that are not identically zero.

## Depends on

- [Congruence subgroup $\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/congruence-subgroup-gamma1.md), for the group under which a modular form of weight $k$ is invariant
- [Congruence subgroup $\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/congruence-subgroup-gamma0.md), for the transformation law with the character $\varepsilon$
- [Cusp form](../../../modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/cusp-form.md), for the cusp forms of weight $k$ for $\Gamma_1(N)$
- [Eigenvector of a linear map](../../../../LinearAlgebra/eigenvalues-and-canonical-forms/eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/has-eigenvector.md), for eigenvectors, which are nonzero

## Proof depends on

This node has no prerequisites.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §1.1, pp. 507–508, for $\Gamma_1(N)$ and
  $\Gamma_0(N)$; §1.2, p. 508, for modular forms and cusp forms of weight $k$ on a subgroup of
  $\mathbf{SL}_2(\mathbf{Z})$ containing $\Gamma(N)$; §1.3, p. 508, for the $q$-expansion of a modular form on
  $\Gamma_1(N)$; §1.5, pp. 508–509, for Dirichlet characters and forms of type $(k, \varepsilon)$ ("On appelle forme
  modulaire de type (k, ε) sur Γ₀(N) une forme modulaire f de poids k sur Γ₁(N) telle que"), and for the remark that a
  character and a weight of different parities would force $f = 0$; formula (1.6.1), p. 509, for $T_p$, $p \nmid N$;
  Théorème 4.1, p. 513, and Proposition 5.1, p. 518, whose eigenvectors $f$ are "non identiquement nulle".
