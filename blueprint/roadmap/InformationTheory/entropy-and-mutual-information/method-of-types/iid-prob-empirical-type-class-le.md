# The type class of $P$ is the most likely one under $P^n$

For $n$-types $s, t$, with $P$ the empirical distribution of $s$,

$$P^n(T_t) \le P^n(T_s).$$

Writing $k_a$ and $j_a$ for the letter counts of $s$ and $t$, this reduces, through the
[size of a type class](card-type-class-mul-prod-factorial.md), to
$\prod_a k_a^{j_a}/j_a! \le \prod_a k_a^{k_a}/k_a!$, which follows coordinatewise from
[a factorial inequality](pow-mul-factorial-le.md). Csiszár's 1998 proof states it ("the first
equality can be checked by simple algebra"); the tutorial proves it by the same exchange argument
("the largest term").

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, proof of Lemma II.2.
- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, proof of Lemma 2.2.
