# One-step change of the stored battery energy

In a ledger with initial stocks $s^0_i$ and per-step flows $f_i(k)$, the stock of resource $i$ after $t$ steps is $S_i(t) = s^0_i + \sum_{k < t} f_i(k)$. If resource $e$ has the battery flow $f_e(k) = \Delta t_k\,(\eta_c P^c_k - P^d_k/\eta_d)$ (for $\eta_d = 0$ this takes the convention $x/0 = 0$), then for every $k$,

$$S_e(k+1) = S_e(k) + \Delta t_k \left(\eta_c P^c_k - \frac{P^d_k}{\eta_d}\right).$$
