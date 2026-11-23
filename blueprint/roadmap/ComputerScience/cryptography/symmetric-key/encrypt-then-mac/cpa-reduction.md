# The CPA reduction

Katz and Lindell's adversary against the encryption scheme (Section 4.5) is built from a
chosen-ciphertext adversary against encrypt-then-MAC. It draws a MAC key $k_2$ and the adversary's
coins and runs the adversary, forwarding encryption queries to its own encryption oracle and tagging
the answers with $k_2$. It answers decryption queries with the simulated decryption oracle, which
gives $\bot$ on the challenge and otherwise answers from the table of answers, and each decryption
query costs it one dummy encryption query. It completes its own challenge ciphertext $c$ to
$(c, F(k_2, c))$, which it hands to the adversary's second stage as the challenge.
