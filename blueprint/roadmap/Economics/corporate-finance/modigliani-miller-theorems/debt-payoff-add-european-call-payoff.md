# Debt Payoff add european Call Payoff

Debt plus equity reconstructs the firm: `min V F + max (V - F) 0 = V`. Equity is the
European call `europeanCallPayoff V F` on firm value struck at the face value (limited
liability). Specialization of `min_add_max` and `max_sub_sub_right`; the kernel is not
reproved.
