# Neutral-phase occupancy and arrival laws in multistage carcinogenesis

**Model.** A continuous-time multitype branching process follows a linear pathway $0 \to 1 \to \cdots \to q+1$ from healthy cells (type $0$) to the malignant type $q+1$. A type-$i$ cell divides at rate $b_i$, dies at rate $d_i$ and mutates into type $i+1$ at rate $u_i$ (the mutating cell changes type); $\lambda_i = b_i - d_i$. Types $0, \dots, k$ are at homeostasis ($\lambda_i = 0$; here $b_i = d_i = 0$) and types $k+1, \dots, q$ grow ($\lambda_i > 0$). The process starts from $N_0(0) = N$ healthy cells, and the mutation rates $u_0, \dots, u_k$ are pairwise distinct.

**Proposition (neutral types).** Lineages of the $N$ founders are independent, and for $1 \le l \le k$ each lineage is in type $l$ at time $t$ with probability

$$p_l(t) = P(\tau'_l \le t < \tau'_{l+1}) = \Big(\prod_{i=0}^{l-1} u_i\Big) \sum_{i=0}^{l} \frac{e^{-u_i t}}{\prod_{j \ne i,\, j \le l} (u_j - u_i)},$$

where $\tau'_{l+1} = \sum_{i=0}^{l} \mathrm{Exp}(u_i)$ is the arrival time of type $l+1$ in one lineage (a hypoexponential law with density $\sum_{i=0}^l \prod_{j \ne i} \frac{u_j}{u_j - u_i}\, u_i e^{-u_i x}$). Hence $N_l(t) \sim \mathrm{Binomial}(N, p_l(t))$ and, for small mutation rates,

$$p_l(t) = \frac{\prod_{i=0}^{l-1} u_i\; t^l}{l!} + O\big(\|u\|^{l+1}\big), \qquad \mathbb E[N_l(t)] \approx N \prod_{i=0}^{l-1} u_i \frac{t^l}{l!},$$

the Armitage–Doll power law of cancer incidence.

**Lemma 1 (first growing type).** In a single lineage, let $N^{*\prime}_{k+1}$ be the type-$(k+1)$ count of the approximating process in which type-$k+1$ cells do not mutate further (the source's $Z^*_{k+1}$; in the true process, for $u_{k+1}>0$, the clone grows at rate $\lambda_{k+1}-u_{k+1}$ and the limit below is $0$). Then almost surely

$$\lim_{t \to \infty} e^{-\lambda_{k+1} t} N^{*\prime}_{k+1}(t) = X_{k+1} := V_{k+1} e^{-\lambda_{k+1}\tau'_{k+1}},$$

where $V_{k+1}$ is the limit for a clone founded at time $0$. If moreover type $k+1$ does not die ($d_{k+1} = 0$, the source's assumption A2), so that $\mathbb E\big[e^{-\theta V_{k+1}}\big] = 1/(1+\theta)$, then

$$\mathbb E\big[e^{-\theta X_{k+1}}\big] = \sum_{i=0}^k \Big(\prod_{j \ne i} \frac{u_j}{u_j - u_i}\Big)\, {}_2F_1\Big(1, \frac{u_i}{\lambda_{k+1}}; 1 + \frac{u_i}{\lambda_{k+1}}; -\theta\Big).$$

Later growing types inherit Laplace transforms of the same form by rescaling $\theta$, which yields approximate laws for the arrival time of the malignant type.

## Expansion

Without division or death in the homeostatic phase, each founder lineage is a single cell that moves along the pathway after independent exponential waiting times, so being in type $l$ at time $t$ means having made exactly $l$ of the steps. Subtracting $P(\tau'_{l+1} \le t)$ from $P(\tau'_l \le t)$, both given by partial-fraction sums of exponentials, gives $p_l$; the divided-difference identity $\sum_i e^{-u_i t}/\prod_{j\ne i}(u_j - u_i) = t^l/l! + O(\|u\|)$ gives the power law. Once a lineage enters the first growing type it starts a supercritical clone whose size divided by $e^{\lambda_{k+1} t}$ converges, shifted by the random entry time; averaging $e^{-\theta V e^{-\lambda \tau}}$ over the hypoexponential $\tau$ produces the hypergeometric terms. The model is applied to the initiation of colorectal cancer and to the incidence of chronic myeloid leukemia.

## Sources

- R. Zhang, I. Bozic, "Accumulation of Oncogenic Mutations During Progression from Healthy Tissue to Cancer", Bulletin of Mathematical Biology 86(12) (2024) 142, model (1), Equation (2), Appendix A.1 Equations (A5)-(A7) and Lemma 1, <https://doi.org/10.1007/s11538-024-01372-3>, PMCID PMC11522190.
