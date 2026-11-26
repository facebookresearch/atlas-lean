# Line-to-line voltages of three phase voltages

For complex phase voltages `(V_a, V_b, V_c)` indexed by the integers mod 3, the line-to-line
voltages are the differences

`(V_ab, V_bc, V_ca) = (V_a - V_b, V_b - V_c, V_c - V_a)`,

that is `V_p - V_{p+1}` at index `p`, with the index taken mod 3.
