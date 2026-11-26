# Stored battery energy stays within bounds at every prefix

Consider a ledger of resources $i \in \iota$ with lower bounds $\ell_i$, upper bounds $h_i$, reserves $r_i \ge 0$, initial stocks $s^0_i$ and per-step flows $f_i(k)$, and a horizon $N$. The ledger is prefix-feasible if for every resource $i$ and every $t \le N$,

$$\ell_i + r_i \le s^0_i + \sum_{k < t} f_i(k) \le h_i.$$

Let $e$ be a resource whose flow is the battery flow $f_e(k) = \Delta t_k\,(\eta_c P^c_k - P^d_k/\eta_d)$, for step lengths $\Delta t_k$, charge and discharge powers $P^c_k, P^d_k$ and efficiencies $\eta_c, \eta_d$ (for $\eta_d = 0$ the flow takes the convention $x/0 = 0$). If the ledger is prefix-feasible, then for every $t \le N$,

$$\ell_e + r_e \le s^0_e + \sum_{k < t} \Delta t_k \left(\eta_c P^c_k - \frac{P^d_k}{\eta_d}\right) \le h_e.$$
