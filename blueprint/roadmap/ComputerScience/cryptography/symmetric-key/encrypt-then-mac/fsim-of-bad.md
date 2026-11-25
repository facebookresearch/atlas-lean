# At the first bad query the forger wins

Suppose the challenge, if any, and every entry of the starting table carry valid tags. If the
simulated game records its first bad query at index $j$, then the forger guessing $j$ outputs a pair
$(c, t)$ with $t = F(k_2, c)$, where $c$ was never asked to the MAC oracle and differs from the
ciphertext of every table entry and from the challenge ciphertext.
