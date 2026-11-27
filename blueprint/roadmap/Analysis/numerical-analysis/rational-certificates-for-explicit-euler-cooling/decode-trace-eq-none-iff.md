# Rejection by the trace decoder

A token is spelled as an optional `-`, a numerator digit run, the character `/`, and a denominator digit run. It is admissible when both digit runs consist of one to eleven decimal digits, the signed numerator $z$ it denotes satisfies $|z| \le 10^{10}$, and the denominator $d$ it denotes satisfies $1 \le d \le 10^{10}$ (leading zeros allowed, `-0` denoting $0$).

The bounded trace decoder returns no value on a character list $s$ if and only if it is not the case that $s$ has at most $300$ characters and $s$ is the comma-joined spelling $t_1,t_2,\dots,t_{11}$ of eleven admissible tokens.
