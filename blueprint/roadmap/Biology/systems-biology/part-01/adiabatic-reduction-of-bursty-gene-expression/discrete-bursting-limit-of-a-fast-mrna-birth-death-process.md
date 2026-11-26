# Discrete bursting limit of a fast-mRNA birth–death process

Let $(X_1,X_2)$ be a continuous-time Markov chain on $\mathbb{N}^2$ (mRNA and protein copy numbers) with reactions

$$\emptyset\xrightarrow{\lambda_1(X_1,X_2)}X_1,\quad X_1\xrightarrow{\gamma_1(X_1,X_2)}\emptyset,\quad \emptyset\xrightarrow{\lambda_2(X_1,X_2)}X_2,\quad X_2\xrightarrow{\gamma_2(X_1,X_2)}\emptyset .$$

Speed up mRNA degradation and translation: $\gamma_1^N=N\gamma_1$, $\lambda_2^N=N\lambda_2$, and let $(X_1^N,X_2^N)$ be the rescaled chain.

**Hypotheses.** (1) $\gamma_2(X_1,0)\equiv0$; (2) $\gamma_1(0,X_2)\equiv0$ and $\inf_{X_1\ge1,X_2\ge0}\gamma_1(X_1,X_2)>0$; (3) $\lambda_2(0,X_2)=0$; (4) $\lambda_1,\lambda_2$ are bounded by a linear function of $X_1+X_2$; (5) $\lambda_1$ or $\lambda_2$ is bounded.

**Statement.** If $(X_1^N(0),X_2^N(0))\Rightarrow(0,X(0))$, then for every $T>0$, $(X_1^N,X_2^N)$ converges in $L^p(0,T)$, $1\le p<\infty$, to $(0,X)$, where $X$ is the one-dimensional bursting process with generator

$$\mathcal{B}_\infty\varphi(x)=\lambda_1(0,x)\Big(\int_0^\infty P_t\big(\gamma_1(1,\cdot)\varphi\big)(x)\,dt-\varphi(x)\Big)+\gamma_2(0,x)\big[\varphi(x-1)-\varphi(x)\big],$$

$$P_tg(x)=\mathbb{E}\Big[g\big(Y(t,x)\big)\,e^{-\int_0^t\gamma_1(1,Y(s,x))\,ds}\Big],$$

and $Y(\cdot,x)$ is the pure birth process started at $x$ with generator $Ag(y)=\lambda_2(1,y)\,(g(y+1)-g(y))$.

For the linear mRNA–protein model, $\gamma_1=g_1X_1$ and $\lambda_2=k_2X_1$, the burst kernel is explicit: $\int_0^\infty P_t(\gamma_1\varphi)(y)\,dt=\frac{g_1}{g_1+k_2}\sum_{z\ge0}\varphi(y+z)\big(\frac{k_2}{k_2+g_1}\big)^z$, i.e. each transcription event adds a geometric burst of protein with parameter $k_2/(k_2+g_1)$.

## Expansion

Each mRNA molecule lives for a time of order $1/N$ and during it produces of order one protein (translation rate $N\lambda_2$), so at the slow time scale the protein jumps by a random burst whose law is the number of births of $Y$ before the killing clock $\gamma_1(1,\cdot)$ rings. The proof is a martingale argument: moment bounds, tightness of the protein component (the mRNA component converges only in $L^p$ in time, not in the Skorokhod topology), and identification of the limit through the martingale problem for $\mathcal{B}_\infty$. Hypotheses (1)–(3) encode positivity and the mRNA-dependence of translation; (4)–(5) prevent explosion.

## Sources

- R. Yvinec, *Adiabatic reduction of models of stochastic gene expression with bursting*, arXiv:1301.1293 (2013), <https://doi.org/10.48550/arXiv.1301.1293>. Theorem 1 and the remark following it (geometric burst sizes).
