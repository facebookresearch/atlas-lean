# The lucky set of a word

Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car
$i$ prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when
every $w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in
order, and car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an
earlier car, or in $p(i) = q_i$ if there is no such spot. The lucky set $\mathrm{Lucky}(w)$
is the set of cars $i \in \{1, \dots, 2n\}$ with $p(i) = w_i$; when every $w_i$ lies in
$\{1, \dots, 2n\}$, these are the cars that park in their preferred spot.

## Sources

- L. Colmenarejo et al., *On the Lucky and Displacement Statistics of Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7, Definition 1.2.
