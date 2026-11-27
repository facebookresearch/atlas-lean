# Galois representations attached to normalized eigenforms

Let
$f \in S_k(\Gamma_1(N))$ be a normalized eigenform with nebentypus $\chi$, so $a_1(f) = 1$, $f$ is
an eigenform for every Hecke operator $T_n$ and diamond operator $\langle d \rangle$, and
$f|_k\gamma = \chi(d)\,f$ for $\gamma = \left(\begin{smallmatrix} a & b \\ c & d
\end{smallmatrix}\right) \in \Gamma_0(N)$. Let $K_f = \mathbb{Q}(a_n(f) : n \ge 0) \subseteq
\mathbb{C}$ be its number field, $\ell$ a prime and $\lambda$ a maximal ideal of
$\mathcal{O}_{K_f}$ lying over $\ell$. Then there is an irreducible continuous representation

$$\rho_{f,\lambda} \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to
\operatorname{GL}_2(K_{f,\lambda}),$$

unramified at every prime $p \nmid \ell N$, such that for every maximal ideal $\mathfrak{p}$ of
$\overline{\mathbb{Z}}$ over such a $p$ the characteristic polynomial of
$\rho_{f,\lambda}(\operatorname{Frob}_{\mathfrak{p}})$ is

$$x^2 - a_p(f)\,x + \chi(p)\,p^{k-1}.$$

Conventions. A normalized eigenform with nebentypus $\chi$ is `CuspForm.IsEigenformWith χ f`, and
$a_n(f)$ is the coefficient of $q^n$, $q = e^{2\pi i\tau}$. The field $K_f$ is the argument `K`,
pinned by `hK`; that it is a number field is a presupposition of the theorem, taken as an instance
argument. $K_{f,\lambda}$ is the completion of $K_f$ at $\lambda$, and the absolute Galois group
carries the Krull topology. Irreducible means that no line of $K_{f,\lambda}^2$ is stable under
every $\rho_{f,\lambda}(\sigma)$. $\overline{\mathbb{Z}}$ is the integral closure of $\mathbb{Z}$ in
$\overline{\mathbb{Q}}$. Unramified at $p$ means that the inertia group of every $\mathfrak{p}$ over
$p$, the elements acting trivially on $\overline{\mathbb{Z}}/\mathfrak{p}$, acts trivially. An
arithmetic Frobenius at $\mathfrak{p}$ is any $\sigma$ acting as $x \mapsto x^p$ on
$\overline{\mathbb{Z}}/\mathfrak{p}$. For each such $p$ the theorem asserts elements `a` and `b`
of $K_f$ whose complex values are $a_p(f)$ and $\chi(p)\,p^{k-1}$, so both coefficients lie in
$K_f$, and the characteristic polynomial is formed from them; the unramifiedness clause does not
depend on them. The theorem has no weight hypothesis: for $k \ge 2$ the representation is due to
Deligne, for $k = 1$ to Deligne and Serre (P. Deligne and J.-P. Serre, *Formes modulaires de
poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530), and for $k \le 0$ there are no
nonzero cusp forms.

## Sources

- Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer (2005), [Theorem 9.6.5, p. 393](https://doi.org/10.1007/978-0-387-27226-9), with normalized eigenforms as in Definition 5.8.1 and Galois representations, unramifiedness and absolute Frobenius elements as in Section 9.3 (Definitions 9.3.2 and 9.3.3).
