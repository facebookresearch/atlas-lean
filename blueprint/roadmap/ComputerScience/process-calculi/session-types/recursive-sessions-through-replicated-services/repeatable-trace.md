# Every round count has a trace returning to the pending state

Let $b$ be a name and $m$ a natural number, and put $L = 3(m+1)$. There are processes $f_0, \dots,
f_L$ with $f_0 = f_L = P(b)$, $f_i \to f_{i+1}$ for every $i < L$, and $f_{3j+2} = P_2(b)$ and
$f_{3j+3} = P(b)$ for every $j \le m$.

The states are $P(b) = (Q_s(b) \mid D_s) \mid (Q_r(b) \mid D_r)$, $P_1(b) = (W_s(b) \mid D_s) \mid
(Q_r(b) \mid D_r)$ and $P_2(b) = (W_s(b) \mid D_s) \mid (W_r(b) \mid D_r)$. Here $W_s(b) =
\overline{b}\langle \mathrm{c}_{712}\rangle.\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$
and $W_r(b) = b(\cdot).\overline{\mathrm{c}_{711}}\langle \uparrow_0 b\rangle.\mathbf{0}$ are the
workers, $D_s = {!\mathrm{c}_{710}(\cdot).W_s(\mathrm{v}_0)}$ and $D_r =
{!\mathrm{c}_{711}(\cdot).W_r(\mathrm{v}_0)}$ the replicated daemons, and $Q_s(b) =
\overline{\mathrm{c}_{710}}\langle b\rangle.\mathbf{0}$ and $Q_r(b) =
\overline{\mathrm{c}_{711}}\langle b\rangle.\mathbf{0}$ the requests.
