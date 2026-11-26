# Joint transform of extinction time and infection count

**Model.** In a closed population of size $N$ with $P$ intervention phases, the state is $X(t) = (S(t), I(t), J(t))$, with $R = N - S - I$ and $J(t) \in \{1, \dots, P\}$ the active phase. In state $(s, i, p)$ the transitions are

- infection $(s,i,p) \to (s-1, i+1, p)$ at rate $\frac{b_p}{N}si$;
- recovery $(s,i,p) \to (s, i-1, p)$ at rate $\gamma_p i$;
- direct immunization $(s,i,p) \to (s-1, i, p)$ at rate $\psi_p s$;
- phase change $(s,i,p) \to (s,i,p')$ at rate $\lambda_{p,p'}(s,i)$, which may depend on the epidemic state.

The extinction time is $T = \inf\{t : I(t) = 0\}$, and $N^I$ is the number of infections before $T$. Since $S$ never increases, the transient states are ordered in levels $L(s)$ and the generator restricted to them is block lower bidiagonal.

**Lemma.** If $\gamma_* = \min_p\gamma_p > 0$, then $T < \infty$ almost surely from every transient state, and there is $\eta_T > 0$ with $\sup_{(s,i,p)}\mathbb E[e^{\eta T} \mid (s,i,p)] < \infty$ for $0 \le \eta < \eta_T$; all moments of $T$ are finite.

**Theorem.** Fix $0 < \eta_0 < \min\{\eta_T, \gamma_*\}$ and let $\Phi_{s,i,p}(z,u) = \mathbb E[e^{-zT}u^{N^I} \mid (s,i,p)]$ for $\mathrm{Re}(z) > -\eta_0$ and $u \in \mathbb C$. Write $\mathbf B = \mathrm{diag}(b_p)$, $\boldsymbol\Gamma = \mathrm{diag}(\gamma_p)$, $\boldsymbol\Psi = \mathrm{diag}(\psi_p)$, $\mathbf Q_P(s,i) = (\lambda_{p,p'}(s,i))$ (with diagonal minus the row sums), and
$$\mathbf A_{s,i}(z) = z\mathbf I_P + \frac{si}{N}\mathbf B + i\boldsymbol\Gamma + s\boldsymbol\Psi - \mathbf Q_P(s,i).$$
Then $\mathbf A_{s,i}(z)$ is nonsingular, $\boldsymbol\Phi_{s,0} = \mathbf 1_P$, $\mathbf A_{0,i}(z)\boldsymbol\Phi_{0,i} = i\boldsymbol\Gamma\boldsymbol\Phi_{0,i-1}$, and for $s \ge 1$, $1 \le i \le N - s$,
$$\mathbf A_{s,i}(z)\boldsymbol\Phi_{s,i}(z,u) = i\boldsymbol\Gamma\boldsymbol\Phi_{s,i-1}(z,u) + s\boldsymbol\Psi\boldsymbol\Phi_{s-1,i}(z,u) + u\frac{si}{N}\mathbf B\boldsymbol\Phi_{s-1,i+1}(z,u),$$
solved by increasing $s$ and, within each level, increasing $i$. Equivalently, the vector $\boldsymbol\Phi$ is the unique solution of $(z\mathbf I - \mathbf Q_{T,T}(u))\boldsymbol\Phi = \mathbf Q_{T,a}\mathbf 1$, where $\mathbf Q_{T,T}(u)$ multiplies infection transitions by $u$.

Analogous level-wise linear recursions give all mixed moments of $T$ and $N^I$, and expanding in powers of $u$ gives the exact distribution of the number of infections and conditional extinction-time transforms.

## Expansion

First-step analysis from $(s,i,p)$ gives one linear equation per state; because infections and immunizations lower $s$ and recoveries lower $i$, the only coupling within a pair $(s,i)$ is through the $P$ phases, so each step solves a $P \times P$ system instead of the full $|S_T|$-dimensional one. Exponential moments of $T$ follow because recovery at rate at least $\gamma_*$ per infective and the finite number of possible infections bound the time to extinction by a sum of finitely many exponential phases. State-dependent switching lets escalation or relaxation of control respond to prevalence, while keeping the computation exact.

## Sources

- V. E. Papageorgiou, I. Votsi and S. Trevezas, "Evaluating the Impact of Epidemic Control via State-Dependent Markovian Switching Modeling", arXiv preprint (2026), Section 2, Lemma 1, Theorem 2, Corollary 3 and Theorem 4. <https://doi.org/10.48550/arXiv.2607.18364>