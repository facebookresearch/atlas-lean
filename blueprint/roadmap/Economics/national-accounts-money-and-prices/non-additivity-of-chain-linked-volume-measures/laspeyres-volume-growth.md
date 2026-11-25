# Laspeyres volume growth between consecutive periods

The Laspeyres volume growth from one period to the next, over a finite set of
goods, weights the quantity change by previous-period prices:
`(∑_i p_prev(i) * q_curr(i)) / (∑_i p_prev(i) * q_prev(i))`, with values in a
field and the convention `x / 0 = 0`.
