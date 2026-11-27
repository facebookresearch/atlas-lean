# The hard-core experiment, distinguishing form

Draw a key pair $(\alpha, \tau)$, coins $r$ and a uniform $x \in D$. The distinguisher receives
$\alpha$, $p_\alpha(x)$ and the bit $b_\alpha(x)$ (world $0$) or its complement (world $1$), and the
experiment outputs its answer.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.3.4, proof of Proposition 5.3.14 (the ensembles $(\alpha, p_\alpha(r), b(r))$ and
  $(\alpha, p_\alpha(r), 1 \oplus b(r))$).
