# The sorted rearrangement of a uniquely encoded parking function

The statistic encoding
of $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ is the word over $\{A, D, T\}$ whose letter at
each position $0 \le i \le n - 2$ is $A$, $D$ or $T$ according as $f(i) < f(i+1)$,
$f(i) > f(i+1)$ or $f(i) = f(i+1)$. Let $f$ be a parking function of length $n$ such that every
parking function of length $n$ with the same statistic encoding equals $f$, and let
$\beta : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ be nondecreasing and take each value as often
as $f$ does. Then the statistic encoding of $\beta$ consists of $A$'s followed by $T$'s (either
block may be empty).

## Sources

- Ari Cruz, Pamela E. Harris, Kimberly J. Harry, Jan Kretschmann, Matt McClinton, Alex Moon, John O. Museus and Eric Redmon, *On Some Discrete Statistics of Parking Functions*, Journal of Integer Sequences 27 (2024), Article 24.8.6, Lemma 50 (`jis-2024-24.8.6-lem-50`).
