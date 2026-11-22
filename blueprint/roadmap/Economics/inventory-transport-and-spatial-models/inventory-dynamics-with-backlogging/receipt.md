# Receipt

Scheduled receipt at period `t`.

Event order per period: receive the scheduled quantity, place an order,
receive that new order immediately if `L = 0`, then serve demand.
Single guarded rule: initial-pipeline coordinate `t` if `t < L`, else
order `t - L`. For `L = 0` this gives order `t` (since `t - 0 = t`).
