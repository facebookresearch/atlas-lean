# Counting palindromes by filling the gaps in odd-length prefixes

Let $b$, $k$, $q$, and $r$
be natural numbers with $b \ge 2$, $k \ge 1$, and $b \equiv 1 \pmod q$. Write $A_b(b^k,q,r)$ for the
count of positive base-$b$ palindromes up to $b^k$ congruent to $r$ modulo $q$. Put
$S = b^{\lfloor k/2 \rfloor}$ and $T = b^{\lfloor (k-1)/2 \rfloor}$. Let $C(N,c,a)$ count integers
$h$ with $1 \le h \le N$ and $ch \equiv a \pmod q$. Then

$$
A_b(b^k,q,r) + C(T-1,2,r+1) = C(S-1,2,r) + C((b+1)T-2,1,r).
$$

The even-length prefixes range from $1$ to $S-1$ and give the residues $2h$. The odd-length
prefixes range from $1$ to $bT-1$ and give the residues of $h + \lfloor h/b \rfloor$. This latter
sequence spans the interval from $1$ to $(b+1)T-2$, jumping by two whenever $h$ reaches a
multiple $bu$ of $b$. At such a jump the skipped value is $(b+1)u-1$. Since $b \equiv 1 \pmod q$,
the skipped value is congruent to $r$ exactly when $2u \equiv r+1 \pmod q$, giving the correction
term $C(T-1,2,r+1)$.
