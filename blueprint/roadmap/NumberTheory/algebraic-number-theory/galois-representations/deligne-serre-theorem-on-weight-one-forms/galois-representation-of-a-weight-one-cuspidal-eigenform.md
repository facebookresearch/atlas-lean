# Galois representation of a weight-one cuspidal eigenform

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ with $\varepsilon(-1) = -1$, and let $f \ne 0$ be a cusp
form of [type $(1, \varepsilon)$ on $\Gamma_0(N)$](modular-forms-of-type-k-epsilon.md) that is an eigenvector of the
Hecke operators $T_p$, $p \nmid N$, with eigenvalues $a_p$. Then:

1. there is an integer $A \ge 1$ such that for every prime $p \nmid N$

    $$1 - a_p T + \varepsilon(p) T^2 = (1 - \alpha T)(1 - \beta T)$$

    for roots of unity $\alpha$, $\beta$ of order at most $A$; in particular $a_p$ is a sum of two roots of unity;
2. there is a representation $\rho \colon G \to \mathrm{GL}_2(\mathbb{C})$, $G = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$,
   continuous for the discrete topology of $\mathbb{C}$, hence with finite image, unramified outside $N$, such that

    $$\det(1 - F_{\rho,p} T) = 1 - a_p T + \varepsilon(p) T^2 \qquad \text{for every prime } p \nmid N,$$

    that is, $\operatorname{Tr}(F_{\rho,p}) = a_p$ and $\det(F_{\rho,p}) = \varepsilon(p)$, with unramified and $F_{\rho,p}$ as on
    [Semisimple Galois representations with the same Frobenius polynomials](semisimple-galois-representations-with-equal-frobenius-polynomials.md).

This is the cuspidal case of Théorème 4.1 of Deligne–Serre without its irreducibility clause, which is
[Irreducibility of the Galois representation of a weight-one cusp form](irreducibility-of-the-galois-representation-of-a-weight-one-cusp-form.md);
part 1 is shown in §8.5 and part 2 in §8.6.

Their proof, in the notation of
[the representations modulo ℓ](representations-mod-l-of-a-weight-one-cuspidal-eigenform.md). (8.5) Let $A$ be as in
[the uniform bound](uniform-bound-on-the-images-of-the-representations-mod-l.md), enlarge $K$ (which shrinks $L$) so
that it contains the $n$-th roots of unity for all $n \le A$, and let $Y$ be the finite set of polynomials
$(1 - \alpha T)(1 - \beta T)$ with $\alpha$, $\beta$ roots of unity of order at most $A$. For $p \nmid N$ and every
$\ell \in L$ with $\ell \ne p$, $1 - a_p T + \varepsilon(p) T^2$ is congruent modulo $\lambda_\ell$ to an element of $Y$;
as $Y$ is finite, one $R \in Y$ serves for infinitely many $\ell$, and then $1 - a_p T + \varepsilon(p) T^2 = R(T)$.
(8.6) Let $L'$ be the set of $\ell \in L$ with $\ell > A$ such that distinct elements of $Y$ stay distinct modulo
$\lambda_\ell$; $L \smallsetminus L'$ is finite. For $\ell \in L'$ the order of $G_\ell$ is prime to $\ell$, so the identity
representation $G_\ell \to \mathrm{GL}_2(\mathbb{F}_\ell)$ is the reduction modulo $\lambda_\ell$ of a representation
$G_\ell \to \mathrm{GL}_2(\mathcal{O}_{\lambda_\ell})$, $\mathcal{O}_{\lambda_\ell}$ the valuation ring of $\lambda_\ell$; composed with
$G \to G_\ell$ it gives $\rho \colon G \to \mathrm{GL}_2(\mathcal{O}_{\lambda_\ell}) \subset \mathrm{GL}_2(\mathbb{C})$, unramified outside
$N\ell$. For $p \nmid N\ell$ the eigenvalues of $F_{\rho,p}$ are roots of unity of order at most $A$, so
$\det(1 - F_{\rho,p} T) \in Y$; it is congruent modulo $\lambda_\ell$ to $1 - a_p T + \varepsilon(p) T^2$, also in $Y$, so the two
are equal. The same construction at another $\ell' \in L'$ gives $\rho'$ with the same polynomials for $p \nmid N\ell\ell'$,
so $\rho \cong \rho'$ by
[the lemma on Frobenius polynomials](semisimple-galois-representations-with-equal-frobenius-polynomials.md); hence $\rho$
is unramified outside $N$ and the equality holds for every $p \nmid N$.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for cusp forms of type $(1, \varepsilon)$ and the operators $T_p$
- [Semisimple Galois representations with the same Frobenius polynomials are isomorphic](semisimple-galois-representations-with-equal-frobenius-polynomials.md), for the conventions on unramified representations and Frobenius elements

## Proof depends on

- [Representations modulo ℓ attached to a weight-one cuspidal eigenform](representations-mod-l-of-a-weight-one-cuspidal-eigenform.md), for the $\rho_\ell$ and their Frobenius polynomials
- [Uniform bound on the images of the representations modulo ℓ](uniform-bound-on-the-images-of-the-representations-mod-l.md), for the constant $A$
- [Semisimple Galois representations with the same Frobenius polynomials are isomorphic](semisimple-galois-representations-with-equal-frobenius-polynomials.md), for $\rho \cong \rho'$
- [Chebotarev density theorem](../../adeles-class-field-theory/chebotarev-density-theorem.md), applied to the Galois extension $K$ of $\mathbb{Q}$ with $C = \{1\}$, for the infinitude of $L$ (§§8.5–8.6): the primes that split completely in $K$ have Dirichlet density $1/[K : \mathbb{Q}] > 0$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the lifting of a representation of a finite group of order at most $A$ and prime to $\ell$ from $\mathbb{F}_\ell$ to
  the valuation ring $\mathcal{O}_{\lambda_\ell}$ ("par un argument standard", Deligne–Serre, §8.6), stated with the
  hypothesis of §8.5 that $K$ contains the $n$-th roots of unity for all $n \le A$: the residue field $\mathbb{F}_\ell$
  alone does not suffice, as the character of order $3$ of $\mathbb{Z}/3\mathbb{Z}$ that sends a generator to
  $2 \in \mathbb{F}_7^\times$ does not lift to $\mathbb{Z}_{(7)}^\times$, which has no element of order $3$;
- the eigenvalues of an element of a finite group of order at most $A$ in a representation, roots of unity of order at
  most $A$, and their reduction modulo $\lambda_\ell$ to the roots of unity of $\mathbb{F}_\ell$, which gives the congruence
  of §8.5 for $\ell \ne p$;
- the finiteness of $L \smallsetminus L'$, which is separate from the infinitude of $L$: for each of the finitely many
  pairs $R \ne S$ of elements of $Y$, some coefficient of $R - S$ is a nonzero element of $\mathcal{O}_K$, which lies in
  only finitely many prime ideals of $\mathcal{O}_K$, hence in $\lambda_\ell$ for only finitely many $\ell$; the same
  fact turns the congruences of §8.5 modulo $\lambda_\ell$ for infinitely many $\ell$ into an equality.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §8.5, pp. 525–526 ("autrement dit les polynômes
  $1 - a_p T + \varepsilon(p) T^2$ appartiennent à Y"); §8.6, p. 526; Théorème 4.1 and (4.1.1), pp. 513–514; Corollaire 4.2,
  p. 514; §3.1, pp. 512–513, for representations into $\mathbf{GL}_2(\mathbf{C})$ with $\mathbf{C}$ discrete.
