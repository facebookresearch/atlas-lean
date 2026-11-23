# Size of a type class

Let $\alpha$ be a finite alphabet. For an $n$-type $s$ with letter counts $k_a$,

$$|T_s| \cdot \prod_{a} k_a! = n!,$$

that is, $|T_s|$ is the multinomial coefficient $n!/\prod_a k_a!$. The proof lets the permutations of the $n$
positions act on a sequence of type $s$: the orbit is the type class
([sequences of the same type are rearrangements](exists-perm-of-seq-type-eq.md)) and the stabiliser has
$\prod_a k_a!$ elements.

## Sources

- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, proof of Lemma 2.2 ($|T_P^n| = n!/(k_1! \cdots k_t!)$).
- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Lemma II.2 (the bounds it implies).
