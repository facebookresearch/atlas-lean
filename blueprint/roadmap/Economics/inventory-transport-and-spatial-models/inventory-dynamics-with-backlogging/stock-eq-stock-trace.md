# Ledger stock as a zero-lead-time inventory trajectory

For resources `i` with initial stocks `s₀(i)` and signed flows `f_i(k)` at steps `k`, the stock
after `t` steps is `s₀(i) + ∑_{k < t} f_i(k)`; the gains are the positive parts `max(f_i(k), 0)` and
the draws the negative parts `max(-f_i(k), 0)`. For every resource `i` and step `t`, the stock after
`t` steps is the net stock `I_t` of the backlogging inventory model with lead time `0`, initial
stock `s₀(i)`, the gains as receipts and the draws as demands: `I_0 = s₀(i)`,
`I_{k+1} = I_k + max(f_i(k), 0) - max(-f_i(k), 0)`.
