# Padovan-like sequence for Schreier sets

For natural numbers $p$ and $q$, the sequence
$a_{p,q,n}$, $n \ge 0$, is defined as follows. If $q \ge 1$ and $n \ge p + q$, then
$a_{p,q,n} = a_{p,q,n-q} + a_{p,q,n-p-q}$. Otherwise, if $p \ge q$, then $a_{p,q,n} = 0$ for
$n < p - q$ and $a_{p,q,n} = 1$ for $n \ge p - q$; and if $p < q$, then $a_{p,q,n} = 1$ for
$n < 2p$ and $a_{p,q,n} = 2$ for $n \ge 2p$.

## Sources

- Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1.
