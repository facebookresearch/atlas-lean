# The CPA reduction's simulation keeps query bounds

The CPA reduction's simulation asks one encryption query per query of the chosen-ciphertext
adversary. So if the adversary satisfies the two-phase query bound with condition $C$ and budget
$N$, and the final step turns outputs $x$ with $C(x, j)$ into outputs satisfying $C'$ with budget
$j$, then the simulation satisfies the two-phase query bound with condition $C'$ and budget $N$.
