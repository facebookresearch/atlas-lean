# Probabilistic polynomial-time Turing machines

A **uniform probabilistic polynomial-time** (PPT) Turing machine is a single finite-control machine $M$ for which there exists a polynomial $q$ with natural-number coefficients such that, for every finite binary input $x$ and **every** random tape $r$, the run of $M$ halts within $q(|x|)$ transitions. The same machine and the same polynomial serve all input lengths. The bound is not an expectation or an almost-sure guarantee. It includes the empty word: the constant term $q(0)$ may pay for transitions even there.

Besides its read-only binary input, finitely many initially blank work tapes and a write-only binary output, $M$ has a read-only tape $r:\mathbb Z\to\{0,1\}$ with its head initially at zero. The transition table reads only the current state and scanned symbols. The bits in distinct cells are independent and fair; revisiting a cell returns its original bit. Once $r$ is fixed, [the run is deterministic](run-eq-iterate.md). For each input $x$, the [probability of the output word](output-law-apply.md) $y$ is the product-measure probability of the tapes for which the output at time $q(|x|)$ is $y$. Halting fixes the configuration, so a larger valid time bound gives the same distribution.

## Sources

- R. Pass and A. shelat, [*A Course in Cryptography*](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf), Cornell University, 2010, Definitions 23.4 (random tape) and 23.5 (running time). The notes write the polynomial bound as $n^c$; the general polynomial here makes the convention at short inputs explicit. Definition 26.8 contrasts a non-uniform family, whose machine may vary with input length.
