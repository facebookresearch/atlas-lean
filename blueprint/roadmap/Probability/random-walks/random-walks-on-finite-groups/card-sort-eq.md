# Bayer–Diaconis formula for $a$-shuffles

An $a$-shuffle of a deck of $n$ cards cuts the deck into $a$ packets (multinomially) and riffles
them together; for $a = 2$ it is the Gilbert–Shannon–Reeds model of an ordinary riffle shuffle.
For $a \ge 1$, Bayer and Diaconis prove that the probability that an $a$-shuffle produces the
arrangement $\pi$ is

$$\frac{\binom{a + n - r}{n}}{a^n}, \qquad r = \text{number of rising sequences of } \pi,$$

where $r = 1 + \#\{k : \text{card } k + 1 \text{ lies before card } k \text{ in } \pi\}$ and
$a + n - r$ is replaced by $0$ when it is negative.

In the inverse description of an $a$-shuffle (Section 3 of the paper), each position receives a
pile label $f(i) \in \{0, \dots, a - 1\}$ uniformly and independently, and the piles are stacked in
label order, each keeping its internal order. The resulting inverse shuffle is the stable sorting
permutation of $f$, so the $a$-shuffle equals $\pi$ exactly when the stable sort of $f$ is
$\pi^{-1}$. For every $n$ and $a$, exactly $\binom{a + n - r}{n}$ of the $a^n$ label maps $f$ give
$\pi$; Lemma 1 of the paper shows that this description generates the same distribution as the
others. The count holds for $a = 0$ too, where for $n \ge 1$ there are no label maps and no
probability is defined.

The proof is the paper's stars-and-bars count, made bijective. With $\sigma = \pi^{-1}$, the maps
$f$ whose stable sort is $\sigma$ are those for which $g = f \circ \sigma$ is monotone and strictly
increases at each descent of $\sigma$ ($\sigma(i+1) < \sigma(i)$); there are $r - 1$ descents.
Adding to $g(k)$ the number of non-descents before $k$ turns these maps into the strictly
increasing maps $\{0, \dots, n-1\} \to \{0, \dots, a + n - r - 1\}$, of which there are
$\binom{a + n - r}{n}$.

The same Lemma 1 says that an $a$-shuffle followed by a $b$-shuffle is an $ab$-shuffle, so $m$
riffle shuffles form one $2^m$-shuffle (Theorem 1). From this formula the paper derives that
$\tfrac32 \log_2 n + \theta$ shuffles are necessary and sufficient, a cutoff (Theorem 2); for
$n = 52$ the total variation distance after $m = 5, 6, 7, 8$ shuffles is $0.924, 0.614, 0.334, 0.167$
(Table 1), whence "seven shuffles".

## Background

- [Cutoff for a family of distance profiles](../../markov-chains/mixing-times-of-markov-chains/has-cutoff.md): the phenomenon that
  Theorem 2 of the paper quantifies for riffle shuffles.
- [Fisher–Yates shuffle](../../../ComputerScience/randomized-algorithms/fisher-yates-shuffle/README.md):
  the exact algorithm for a uniform permutation, against which physical shuffles are measured.

## Sources

- D. Bayer and P. Diaconis, *Trailing the dovetail shuffle to its lair*, Ann. Appl. Probab. 2
  (1992) 294–313, Theorem 3 (with its proof), Lemma 1 and Section 3.
