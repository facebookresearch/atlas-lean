# Recursion for the words $W_i$ of the unsum gap sequence

For each $i$ let $V_i$ be the
word $W_i$ with its first and last digit removed, write $|W|$ for the length of a word $W$, and
denote concatenation of words by juxtaposition. For every $i \ge 2$: if $i$ is odd, then
$W_{i+1} = W_i \, 5 \, V_{i-1} \, 3$; if $i$ is even, then $W_{i+1} = 3 \, V_i \, 5 \, W_{i-1}$;
and in both cases $|W_{i+1}| = |W_i| + |W_{i-1}|$. Moreover $|W_1| = 1$, $|W_2| = 2$, and
$|W_i| = F_{i+1}$ for every $i \ge 1$, where $F_m$ is the $m$-th Fibonacci number ($F_0 = 0$,
$F_1 = 1$).

## Sources

- Bosma, Bruin, Fokkink, Grube, Reuijl, and Tromp, *Using Walnut to Solve Problems from the OEIS*, Journal of Integer Sequences 28 (2025), Article 25.3.8, Lemma 8 (`jis-2025-25.3.8-lem-8`).
