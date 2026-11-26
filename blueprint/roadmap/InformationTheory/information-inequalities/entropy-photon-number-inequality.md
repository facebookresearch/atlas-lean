# The entropy photon-number inequality for a bosonic beam splitter

Let $n\ge1$ and let $\rho_A,\rho_B,\rho_C$ be positive trace-one operators on the full number-basis Fock space $\ell^2(\mathbb N^n;\mathbb C)$. Assume $\rho_A$ and $\rho_B$ have finite mean total number, $\sum_k(\sum_{j=1}^n k_j)\langle k|\rho|k\rangle<\infty$. For $0\le\eta\le1$, let $\rho_C$ be the reduced output when the independent input $\rho_A\otimes\rho_B$ is mixed on paired modes by the passive transformation of creation operators

$$
a^\dagger\mapsto\sqrt\eta\,c^\dagger-\sqrt{1-\eta}\,d^\dagger,\qquad
b^\dagger\mapsto\sqrt{1-\eta}\,c^\dagger+\sqrt\eta\,d^\dagger.
$$

In each mode the number-state coefficient is the corresponding binomial expansion coefficient multiplied by $\sqrt{k!e!/(a!b!)}$ for input numbers $(a,b)$ and output numbers $(k,e)$; it is zero unless $k+e=a+b$. Coefficients multiply across modes. The output condition is that each matrix entry of $\rho_C$ equals the convergent series obtained by summing the discarded diagonal number blocks over $e\in\mathbb N^n$; within each block the two input split sums are finite by number conservation.

Apply continuous functional calculus to $\rho$ with the function $z\mapsto -(\operatorname{Re}z)\log(\operatorname{Re}z)$ valued in $\mathbb C$. Define $S(\rho)$ to be the totalized real sum over number states of the real diagonal entries of the resulting operator, with $0\log0=0$. The sum is the totalized real sum (zero if not summable), not a separate trace-class or summability hypothesis for $\rho_C$. Write $g(t)=(t+1)\log(t+1)-t\log t$ for $t\ge0$. The effective photon number is $N(\rho)=g^{-1}(S(\rho)/n)$, with inverse defined as the infimum of nonnegative $t$ having $g(t)\ge S(\rho)/n$. Then $\eta N(\rho_A)+(1-\eta)N(\rho_B)\le N(\rho_C)$. Internal entanglement among the modes of either input is unrestricted.

**Conventions.** Use the full Fock number basis, spectral entropy via the continuous extension of $-t\log t$, and the explicit energy and output entry conditions. A finite-dimensional density-matrix model alone does not express the claimed setting.

## Depends on

- [Bosonic Fock states and the passive beam-splitter output condition](beam-splitter-fock-model.md)

## Expansion

State the passive beam-splitter partial-trace and energy identities and a finite-energy entropy approximation theorem for both the inputs and the output. Identify a valid finite-dimensional entropy comparison and show that the necessary entropy and photon-number quantities pass to the arbitrary finite-energy states. Keep positivity and the number-basis diagonal sums explicit.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EntropyPhotonNumber.lean#L97-L107)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/273.md)
- [Accompanying manuscript: The entropy photon-number inequality](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-entropy-photon-number-inequality-September-24-2026/paper.pdf)
- [Background: Guha, Erkmen and Shapiro, *The entropy photon-number inequality and its consequences* (2008)](https://doi.org/10.1109/ITA.2008.4601037)
