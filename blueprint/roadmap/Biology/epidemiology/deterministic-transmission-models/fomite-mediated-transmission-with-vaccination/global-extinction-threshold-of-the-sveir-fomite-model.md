# Global extinction threshold of the SVEIR fomite model

Consider the [SVEIR model with saturating fomite transmission](sveir-model-with-saturating-fomite-transmission.md) with the Holling type II dose-response $g(C,\kappa)=C/(C+\kappa)$ ($n=1$).

**Theorem.** Let

$$\mathcal J_c=\frac\Lambda\mu\,\frac{\xi}{(\xi+\mu)(\gamma+d+\mu)}\Bigl(\frac{\varphi\alpha_1}{\kappa\omega}+\beta_1\Bigr).$$

If $\mathcal J_c\le1$, the disease-free equilibrium $E_0$ is globally asymptotically stable in $\bar\Omega$. Since $S_0+V_0<\Lambda/\mu$, one has $\mathcal R_c<\mathcal J_c$, so $\mathcal J_c$ is a conservative sufficient condition for elimination.

**Corollary (no vaccination).** For the reduced model without vaccination, with disease-free equilibrium $(\Lambda/\mu,0,0,0)$, the disease-free equilibrium is globally asymptotically stable in $\bar\Omega$ if and only if $\mathcal R_0\le1$, and unstable if $\mathcal R_0>1$; here $\mathcal J_c$ and $\mathcal R_0$ coincide.

## Depends on

- [SVEIR model with saturating fomite transmission](sveir-model-with-saturating-fomite-transmission.md)

## Expansion

The proof applies the Kamgang-Sallet criterion for epidemic systems written as $\dot x_1=A_1(x)(x_1-x_1^*)+A_{12}(x)x_2$, $\dot x_2=A_2(x)x_2$, with $x_2=(E,I,C)$ the infected variables. Point dissipativity on $\Omega$, global stability of the linear disease-free subsystem, and the Metzler irreducible structure of $A_2(x)$ are checked directly. The remaining condition asks for an upper bound $\bar A_2$ of $A_2(x)$ on $\Omega$ with spectral abscissa at most $0$; bounding $S$ and $V$ by $\Lambda/\mu$ and $g(C,\kappa)$ by $C/\kappa$ produces $\bar A_2$, and its stability is equivalent to $\mathcal J_c\le1$. Without vaccination the bound is attained at the disease-free state, which is why the corollary is sharp.

## Sources

- E. Penitente, U. Foryś and B. Gürbüz, "Global stability and uniform persistence in an epidemic model with saturating fomite-mediated transmission", *Ricerche di Matematica* (2026), Section 3.2, Theorem 1, Remark 1, Corollary 1, and Appendix B (Lemma 3, the Kamgang and Sallet criterion), <https://doi.org/10.1007/s11587-026-01159-9> (preprint arXiv:2603.28285).
