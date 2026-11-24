# Arbitrarily long typed repeated-session traces

Let $n$ be a natural number, $r$ a polarity and $b$ a name scoped at depth $n$ (a constant, or a
variable with index $< n$) with $b \ne \mathrm{c}_{710}$ and $b \ne \mathrm{c}_{711}$. Let $m$ be a
natural number and $L = 3(m+1)$. There are processes $f_0, \dots, f_L$ with $f_0 = f_L = P(b)$, $f_i
\to f_{i+1}$ for every $i < L$, $\Gamma_r; I_{b,r} \vdash_n f_i$ for every $i \le L$, and $f_{3j+2}
= P_2(b)$, $f_{3j+3} = P(b)$ for every $j \le m$.

The states are $P(b) = (Q_s(b) \mid D_s) \mid (Q_r(b) \mid D_r)$, $P_1(b) = (W_s(b) \mid D_s) \mid
(Q_r(b) \mid D_r)$ and $P_2(b) = (W_s(b) \mid D_s) \mid (W_r(b) \mid D_r)$. Here $W_s(b) =
\overline{b}\langle \mathrm{c}_{712}\rangle.\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$
and $W_r(b) = b(\cdot).\overline{\mathrm{c}_{711}}\langle \uparrow_0 b\rangle.\mathbf{0}$ are the
workers, $D_s = {!\mathrm{c}_{710}(\cdot).W_s(\mathrm{v}_0)}$ and $D_r =
{!\mathrm{c}_{711}(\cdot).W_r(\mathrm{v}_0)}$ the replicated daemons, and $Q_s(b) =
\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$ and $Q_r(b) =
\overline{\mathrm{c}_{711}}\langle b\rangle.\mathbf{0}$ the requests. The ownership context $I_{b,r}
= \{b^{r} \mapsto \kappa\} \cup \{b^{\bar r} \mapsto \bar\kappa\}$ owns both endpoints of $b$. The
service environment $\Gamma_r$ declares $710 \mapsto (0, r, \kappa)$ and $711 \mapsto (0, \bar r,
\bar\kappa)$ (priority, polarity of the transferred endpoint, capability), where $\kappa = (7,R)$,
$\bar\kappa = (7,\overline{R})$ and $R$ is the cursor at the single node of the one-node graph whose
node sends a name and loops to itself. Finally $\Gamma; \Delta \vdash_n p$ denotes runtime typing
with shared services at depth $n$, service environment $\Gamma$ and ownership context $\Delta$.
