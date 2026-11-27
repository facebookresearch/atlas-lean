# Coalescence and sampling times of an epidemic tree with age-dependent removal form a Markov chain

**Model.** An epidemic starts with one infective at time $0$ and is observed at time $t$. Every infective transmits at constant rate $b$ during its infectious period. The infectious period ends either by recovery without sampling (probability $c_1$, after a random time distributed as $V_1$) or by sampling, i.e. removal together with sequencing (probability $c_2=1-c_1$, after a random time distributed as $V_2$); $V_1$ and $V_2$ are arbitrary distributions on $(0,\infty]$. The population process is a (non-Markovian) splitting tree. Let $q=bc_2$ and define the scale function $W_1^{(q)}$ by its Laplace transform

$$\int_0^\infty e^{-\lambda x}W_1^{(q)}(x)\,dx=\frac1{\psi_1(\lambda)-q},\qquad \psi_1(\lambda)=\lambda-bc_1\int_{(0,\infty]}\bigl(1-e^{-\lambda r}\bigr)P(V_1\in dr),$$

and set $C_1^{(q)}(z)=q\int_0^zW_1^{(q)}(z-u)\,P(V_2\in du)$ and $U_1^{(q)}(z)=1+\int_0^zC_1^{(q)}(s)\,ds$.

Orient the tree of the infectives sampled before $t$ and label sampled tips from left to right; let $S_i\in(0,t]$ be the time (since the start of the epidemic) at which tip $i$ was sampled and $R_i$ the time of the most recent common ancestor of tips $i-1$ and $i$ ($i\ge2$), so that $R_i<\min(S_{i-1},S_i)$.

**Theorem.** The sequence $S_1,(R_2,S_2),(R_3,S_3),\dots$ is a killed Markov chain whose transitions depend only on the previous sampling time. For $x\in(0,t]$, $y\in[0,x)$ and $z\in(y,t)$:

$$P_x(R>y,\,S\in dz)=\Bigl(C_1^{(q)}(z-y)\,\frac{U_1^{(q)}(t-x)}{U_1^{(q)}(t-y)}-\mathbf 1_{\{z\ge x\}}\,C_1^{(q)}(z-x)\Bigr)dz,$$

the chain is killed from state $x$ with probability $k(x)=U_1^{(q)}(t-x)/U_1^{(q)}(t)$, the initial law is

$$P(S_1\in dz)=c_2P(V_2\in dz)+\Bigl(c_2\int_0^zP(V_2\in du)\,W_1^{(q)\prime}(z-u)-\frac{C_1^{(q)}(z)\,C_1^{(q)}(t)}{b\,U_1^{(q)}(t)}\Bigr)dz,$$

and the probability that at least one infective is sampled before $t$ is $p=C_1^{(q)}(t)/(b\,U_1^{(q)}(t))$. Conditioned on $n$ samples, $((R_i,S_i))_{i\le n}$ is a Markov chain with transition kernel $p(x;dy\,dz)/(1-k(x))$.

**Likelihood.** If $V_2$ has a density, $S_1$ has density $g(z)=b^{-1}\bigl(C_1^{(q)\prime}(z)-C_1^{(q)}(z)C_1^{(q)}(t)/U_1^{(q)}(t)\bigr)$ and the transitions have density $f(x;y,z)=\frac{U_1^{(q)}(t-x)}{U_1^{(q)}(t-y)}\bigl[C_1^{(q)\prime}(z-y)-C_1^{(q)}(z-y)\,C_1^{(q)}(t-y)/U_1^{(q)}(t-y)\bigr]$. The likelihood of an oriented sampled tree with coalescence times $(y_i)_{2\le i\le n}$ and sampling times $(z_i)_{1\le i\le n}$, conditional on at least one sample, is

$$\mathcal L_S(\mathcal T)=\frac{g(z_1)\,k(z_n)}{p}\prod_{i=2}^nf(z_{i-1};y_i,z_i),$$

and conditional on exactly $n$ samples each factor $f$ is divided by $1-k(z_{i-1})$. With constant death rate $d$ and sampling rate $\mu$ this reduces to the known birth–death–sampling likelihood.

## Expansion

The contour (jumping chronological contour process) of a splitting tree is a spectrally positive Lévy process with Laplace exponent $\psi(\lambda)=\lambda-b\int(1-e^{-\lambda r})\,\pi(dr)$, reflected below $t$ and killed at $0$: it visits the individuals in depth-first order, jumping up by each lifetime and drifting down at unit speed. Sampled individuals are marked jumps; between two marked jumps the process behaves like the contour of a tree in which only unsampled lifetimes occur (exponent $\psi_1$), killed at rate $q$ when a sampled lifetime would start. Two-sided exit and $q$-resolvent formulas for spectrally positive Lévy processes, expressed through the scale function $W_1^{(q)}$, give the joint law of the minimum of the contour between two consecutive marked jumps (the coalescence time $R$) and the height of the next marked jump (the sampling time $S$); the strong Markov property of the contour at marked jumps yields the Markov chain, and killing corresponds to the contour exiting at $0$ before the next marked jump. This turns a tree that grows non-Markovianly in time into a Markovian process growing horizontally, which also allows fast simulation of sampled trees.

## Sources

- Amaury Lambert, Helen K. Alexander, Tanja Stadler, "Phylogenetic analysis accounting for age-dependent death and sampling with applications to epidemics", arXiv (2013); Journal of Theoretical Biology 352 (2014). Section 4 (Proposition 4.1), Section 5 (Lemma 5.1), Section 6 (Lemmas 6.1 and 6.2, Theorem 6.3, Corollary 6.4), Section 7 (influenza and HIV examples, Proposition 7.2), Appendix (Markovian case). <https://doi.org/10.48550/arXiv.1306.3427>. Published version: Journal of Theoretical Biology 352 (2014), 60–70, <https://doi.org/10.1016/j.jtbi.2014.02.031>; locators above refer to the arXiv version.
