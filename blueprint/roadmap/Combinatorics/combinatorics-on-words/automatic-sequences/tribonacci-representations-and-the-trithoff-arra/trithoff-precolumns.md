# Precolumns of the Trithoff array

Write $[u]_T$ for the Tribonacci value of a digit
word $u$, written most significant digit first. Let $n$ have Tribonacci representation $abc1$,
where $a$ is a digit word and $b$, $c$ are digits. Let $\mathrm{out}(n) = [abc10]_T$ and
$\mathrm{out}^2(n) = [abc100]_T$ be the next two entries of the Trithoff row of $n$, and extend
the row to the left by the Tribonacci rule: in the integers, the wall is
$W = \mathrm{out}^2(n) - \mathrm{out}(n) - n$ and the seed is $S = \mathrm{out}(n) - n - W$.
Then $W = [abc]_T + 1$, $S = [ab]_T + c$, and the pre-seed $n - W - S$ equals $[a]_T + b$.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Lemma 13 (`jis-2025-25.5.4-lem-13`).
