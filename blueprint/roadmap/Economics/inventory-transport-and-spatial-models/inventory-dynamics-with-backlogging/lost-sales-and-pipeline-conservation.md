# Inventory balance with lost sales and a replenishment pipeline

In each period $t$ events occur in the order: receive the scheduled quantity $r_t$, place an order $q_t \ge 0$, serve demand $D_t \ge 0$. With deterministic lead time $L$, $r_t = q_{t-L}$ for $t \ge L$ and $r_t$ comes from the given initial pipeline for $t < L$; for $L = 0$ the order placed in period $t$ is received before demand and $r_t = q_t$. (Backlogging.) Net stock satisfies $I_{t+1} = I_t + r_t - D_t$, with on-hand stock $\max(I, 0)$ and backlog $\max(-I, 0)$. (Lost sales.) With available stock $a_t = I_t + r_t \ge 0$, sales are $\min(a_t, D_t)$, $I_{t+1} = a_t - \min(a_t, D_t)$ and lost demand is $D_t - \min(a_t, D_t)$. In both models, after $T$ periods, initial stock plus total receipts equals final stock plus total demand (backlogging) or total sales (lost sales), and net stock plus the outstanding pipeline (orders placed but not yet received, including those still outstanding at the end) changes in each period by $q_t - D_t$ (backlogging) or $q_t - \min(a_t, D_t)$ (lost sales). The two models are alternatives and are not mixed.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
