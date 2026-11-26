# Regimes of a resource-limited translation network with sequestration

**Network.** Species: free ribosomes $\mathcal R$, sequestered ribosomes $\mathcal R_S$, initiating and elongating ribosome–mRNA complexes $\mathcal{RM}_I,\mathcal{RM}_L$, mRNAs $\mathcal M$, free and charged tRNAs $\mathcal U,\mathcal{UQ}$, amino acids $\mathcal Q$, proteins $\mathcal P$. Reactions:
$$\mathcal R+\mathcal M\xrightarrow{\kappa_{RI}}\mathcal{RM}_I\xrightarrow{\kappa_{IL}}\mathcal{RM}_L,\qquad \emptyset\underset{\kappa_{Q0}}{\overset{\kappa_{0Q}}{\rightleftharpoons}}\mathcal Q,\qquad \mathcal U+\mathcal Q\xrightarrow{\kappa_{QU}}\mathcal{UQ},$$
$$\mathcal R+\mathcal U\xrightarrow{\kappa_{RS}}\mathcal R_S+\mathcal U,\qquad \mathcal R_S\xrightarrow{\kappa_{SR}}\mathcal R,\qquad \mathcal{RM}_L+\mathcal{UQ}\xrightarrow{\kappa_{LR}}\mathcal U+\mathcal R+\mathcal M+\mathcal P .$$
The stochastic model is a Markov jump process with $N$ ribosomes in total, mRNA and tRNA totals $M^0_N/N\to C_M>1$, $U^0_N/N\to C_U>0$, and amino-acid input at rate of order $N$ (input $\kappa_{0Q}N$, initiation completing at rate $\kappa_{IL}$ per complex).

**Without sequestration** (no $\mathcal R_S$). If $\kappa_{0Q}>\kappa_{IL}$, free ribosomes, elongating complexes and free tRNAs are $O(1)$ and amino acids accumulate at order $N$: the network is ribosome-limited. If $\kappa_{0Q}<\kappa_{IL}$, free ribosomes, amino acids and uncharged tRNA deficits are $O(1)$, and the fraction $\ell(t)$ of ribosomes in elongation solves $\dot\ell=\kappa_{IL}-\kappa_{0Q}-\kappa_{IL}\ell$, so a fraction $1-\kappa_{0Q}/\kappa_{IL}$ of ribosomes stalls in elongation. The protein output $P_N(t)/N$ converges to $\kappa_{IL}t$ in the first case and to $\kappa_{0Q}t$ in the second.

**With sequestration.** If $\kappa_{0Q}>\kappa_{IL}$, sequestered and elongating ribosomes are also $O(1)$. If $\kappa_{0Q}<\kappa_{IL}$, set
$$\mathcal C:\qquad \frac{\kappa_{SR}}{\kappa_{RS}}\,\frac{\kappa_{RI}}{\kappa_{0Q}}\Big(C_M-\frac{\kappa_{0Q}}{\kappa_{IL}}\Big)\Big(1-\frac{\kappa_{0Q}}{\kappa_{IL}}\Big)<C_U .$$
Under $\mathcal C$ (optimal sequestration), $R_N,L_N,Q_N$ stay $O(1)$ and the scaled sequestered ribosomes and free tRNAs $(S_N/N,U_N/N)$ converge to the solution of
$$\dot u=\kappa_{IL}(1-s)-\kappa_{0Q},\qquad \dot s=\kappa_{RS}\,u\,\frac{\kappa_{IL}(1-s)+\kappa_{SR}\,s}{\kappa_{RI}(C_M-(1-s))+\kappa_{RS}\,u}-\kappa_{SR}\,s ;$$
few ribosomes are in elongation while almost all resources become protein. If the inequality in $\mathcal C$ is reversed, $R_N,Q_N$ stay $O(1)$ and both $S_N/N$ and $L_N/N$ are of order one: sequestration cannot absorb the ribosome excess.

## Depends on

- [Stable scaling regimes of the stochastic dual phosphorylation network](../thermodynamic-limits-of-stochastic-phosphorylation-networks/stable-scaling-regimes-of-the-stochastic-dual-phosphorylation-network.md)

## Expansion

The $O(1)$ coordinates are fast: conditioned on the slow scaled variables they form a small network of $M/M/\infty$ queues whose invariant law is explicit (for one regime it is not of product form, being the law of $(X+Y_1,Z,X+Y_2)$ for independent Poisson variables). The slow variables obey ODEs averaged against these invariant laws; stopping-time and coupling arguments show the fast coordinates do not escape to order $N$, and a stability analysis of the limiting ODE extends convergence to arbitrary time intervals. In the optimal sequestration regime, free tRNAs act as a sensor: when amino acids are scarce, uncharged tRNAs accumulate and sequester exactly the ribosomes that could not be served.

## Sources

- V. Fromion, P. Robert, J. Zaherddine, "Stochastic Models of Resource Allocation in Chemical Reaction Networks", arXiv:2511.22252 (2025), Section 1.2 (network), Theorems 3 and 4, Proposition 9, Theorem 10, Corollary 11, Theorem 12, Corollary 13, <https://doi.org/10.48550/arXiv.2511.22252>.
