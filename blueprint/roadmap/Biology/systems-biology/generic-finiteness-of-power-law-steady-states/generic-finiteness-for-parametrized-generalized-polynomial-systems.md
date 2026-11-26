# Generic finiteness for parametrized generalized polynomial systems

**Setting.** Let $A\in\mathbb R^{n'\times m}$, a **real** exponent matrix $B\in\mathbb R^{n\times m}$, positive parameters $c\in\mathbb R^m_{>0}$, and consider positive solutions $x\in\mathbb R^n_{>0}$ of
$$A\,(c\circ x^B)=0,\qquad (x^B)_j=\prod_ix_i^{B_{ij}} .$$
Equivalently $(c\circ x^B)\in C$ for the coefficient cone $C=\ker A\cap\mathbb R^m_{>0}$; more generally $C$ may be any positive blunt polyhedral cone (generalized semi-algebraic constraints). Fix a product decomposition $C=C^1\times\dots\times C^\ell$ inducing $\ell$ monomial classes, let $\Delta$ be the corresponding product of standard simplices, and define the **coefficient set** $P=C\cap\Delta$ (a relatively open polytope), the **monomial-dependency subspace** $D=\ker B\cap\ker\mathcal C$ ($\mathcal C$ the $\ell\times m$ Cayley matrix of the classes) with basis matrix $H\in\mathbb R^{m\times d}$, $d=\dim D$, and the monomial difference subspace $L=B(\ker\mathcal C)$. By Müller-Regensburger, the solution set is
$$X_c=(Y_c/c)^E\circ e^{L^\perp},\qquad Y_c=\{y\in P:\ y^H=c^H\},$$
for an explicit exponentiation matrix $E$, so solvability depends only on the $d$ lumped parameters $c^H$, and if $L\ne\mathbb R^n$ every non-empty solution set contains exponential fibers $x\circ e^{L^\perp}$.

**Theorem (generic finiteness).** Let $\varphi:P\to\mathbb R^d$, $\varphi(y)=H^{\mathsf T}\ln y$, so $Y_c=\varphi^{-1}(H^{\mathsf T}\ln c)$. If $\dim P\le d$ (equivalently $\dim L\le\operatorname{rank}A$ for equations, i.e. variables at most equations plus fiber dimension), then the set of good values $V_{\mathrm{good}}\subseteq\mathbb R^d$ is open and dense with null complement, and for every $\gamma\in V_{\mathrm{good}}$ the fiber $\varphi^{-1}(\gamma)$ is finite (empty if $\dim P<d$). Hence for generic $c$, in both the measure and topological sense, there are finitely many exponential fibers of positive solutions. The conclusion persists when only a subset of parameters varies, provided the varying block of $H$ has full rank $d$, and for inequality systems after relaxing $C$ to its linear span or discarding phantom monomials.

**Corollary (power-law dynamics).** For $\dot x=N(c\circ x^V)$ with real stoichiometric matrix $N\in\mathbb R^{n\times m}$, real exponents $V$, and conservation laws $Wx=T$ ($W$ a basis of the left kernel), for generic positive rate constants and generic totals $T$ there are finitely many positive steady states in each stoichiometric compatibility class.

If $\dim P>d$, either $\varphi$ is everywhere critical (then $\varphi(P)$ is null and empty fibers are dense) or some fibers contain submanifolds of dimension $\dim P-d$ on an open set of parameters.

## Depends on

- [Chemical reaction network theory](../chemical-reaction-network-theory/README.md)

## Expansion

Generic finiteness is a properness-plus-Sard argument. Boundary values, limits of $\varphi(y^k)$ along sequences approaching the relative boundary of $P$, form a closed set of dimension at most $\dim P-1\le d-1$; this uses a logarithmic boundary analysis showing that $T\ln q$ along sequences tending to a face of a polytope accumulates on a set of dimension below that of the polytope. Away from boundary values $\varphi$ is proper, so the critical values there form a closed null set by Sard's theorem. At a regular value with $\dim P\le d$ the fiber is a zero-dimensional compact set, hence finite. Unlike algebraic arguments (Bézout, Bernstein-Kushnirenko), the proof does not require integer exponents, which is what power-law models with fitted real kinetic orders need.

## Sources

- S. Müller, "Generic finiteness of solutions to parametrized systems of generalized polynomial inequalities", arXiv:2610.28588 (2026), Section 2 (Lemmas 1-7, Theorem 8, Theorem 9, Corollary 10, Lemma 11, Proposition 12) and Section 3 (Theorems 13-14), <https://doi.org/10.48550/arXiv.2610.28588>.
