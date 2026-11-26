# Trace decoding returns exactly the token values

A token is spelled as an optional `-`, a numerator digit run, the character `/`, and a denominator digit run. It is admissible when both digit runs consist of one to eleven decimal digits, the signed numerator $z$ it denotes satisfies $|z| \le 10^{10}$, and the denominator $d$ it denotes satisfies $1 \le d \le 10^{10}$ (leading zeros allowed, `-0` denoting $0$).

For a character list $s$ and a list $y$ of rationals, the bounded trace decoder returns $y$ on $s$ if and only if $s$ has at most $300$ characters and there are eleven admissible tokens $t_1, \dots, t_{11}$ such that $s$ is their comma-joined spelling $t_1,t_2,\dots,t_{11}$ and

$$y = \left(\tfrac{z_1}{d_1}, \dots, \tfrac{z_{11}}{d_{11}}\right),$$

where $z_i$ and $d_i$ are the numerator and denominator denoted by $t_i$.
