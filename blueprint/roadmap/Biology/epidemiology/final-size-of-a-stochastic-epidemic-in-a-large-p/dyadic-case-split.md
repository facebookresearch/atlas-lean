# A final size between 2ʲ and 2ʲ⁺¹ needs deviating or wasted contacts

Let $S_0$ be a set of initially susceptible individuals of the population $\{0, \dots, N-1\}$ and
$w = (w_1, w_2)$ a [configuration](config.md) whose epidemic has [final size](final-size.md) $F$.
Let $R > 1$ be real and $j \in \mathbb{N}$ with $2^j \le F < 2^{j+1}$, and let
$c = \lfloor 4 R\, 2^j \rfloor$. Then at least one of the following holds:

- the [centered contact count](trunc-dev.md) satisfies $|T_{R,\,2^{j+1}+1}(w)| \ge (R - 1) 2^j / 2$;
- at least $(R - 1) 2^j / 4$ of the first $c$ contacts go outside $S_0$ ([outside contacts](outside-contacts.md));
- at least $(R - 1) 2^j / 4$ of the first $c$ contacts go to an individual contacted before ([repeated contacts](repeat-contacts.md)).
