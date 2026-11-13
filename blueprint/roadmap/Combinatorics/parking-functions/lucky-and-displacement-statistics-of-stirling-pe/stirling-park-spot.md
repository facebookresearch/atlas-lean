# Parking spot of a car

Let $w = w_1 \cdots w_{2n}$ be a word of natural numbers. Car $i$
prefers spot $q_i = ((w_i - 1) \bmod 2n) + 1$, where $w_i - 1$ is truncated at $0$; when every
$w_i$ lies in $\{1, \dots, 2n\}$, this is $q_i = w_i$. Cars $1, \dots, 2n$ arrive in order, and
car $i$ parks in the least spot $p(i) \in \{q_i, \dots, 2n\}$ not taken by an earlier car, or in
$p(i) = q_i$ if there is no such spot. The parking spot of car $i \in \{1, \dots, 2n\}$ is $p(i)$.

## Sources

- L. Colmenarejo et al., *On the Lucky and Displacement Statistics of Stirling Permutations*, Journal of Integer Sequences 27 (2024), Article 24.6.7, Definition 5.1.
