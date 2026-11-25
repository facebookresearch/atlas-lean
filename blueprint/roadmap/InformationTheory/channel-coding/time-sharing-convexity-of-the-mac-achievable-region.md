# Time-sharing convexity of the MAC achievable region

Let $\mathcal{C} = \bigcap_{\varepsilon > 0} \overline{\liminf_{n \to \infty} R^*_n(\varepsilon)}$ be the capacity region of a two-user
discrete memoryless multiple-access channel, where $R^*_n(\varepsilon)$ is the set of rate pairs $R_1, R_2 \ge 0$ admitting an
$(n, M_1, M_2, \varepsilon)$ code with $M_1 \ge 2^{nR_1}$, $M_2 \ge 2^{nR_2}$ and average error at most $\varepsilon$. If
$(R_1, R_2), (R'_1, R'_2) \in \mathcal{C}$ and $\lambda \in [0,1]$ is rational, then
$\lambda(R_1, R_2) + (1-\lambda)(R'_1, R'_2) \in \mathcal{C}$: for each $\varepsilon > 0$, a code of block length
$\lfloor \lambda n \rfloor$ and error $\varepsilon/2$ for the first pair followed by a code of block length $n - \lfloor \lambda n \rfloor$
and error $\varepsilon/2$ for the second is, by the union bound, a code of block length $n$ and error $\varepsilon$ whose
message sizes are the products, and the rounding of block lengths and message sizes costs rates that vanish as
$n \to \infty$, which the closures absorb. Real $\lambda$ then follow because $\mathcal{C}$ is closed.

## Depends on

- [Two-user discrete memoryless multiple-access channel and its capacity region](two-user-discrete-memoryless-multiple-access-channel-and-its.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Lecture notes on information theory*, MIT 6.441, Spring 2016, Definition 26.1 and
  Section 26.3, step 1 of the proof of Theorem 26.1 (convexity of the capacity region by time sharing, with error
  $\varepsilon/2$ per block). <https://ocw.mit.edu/courses/6-441-information-theory-spring-2016/5d8f16adc3385c9ff2975b121bd620e4_MIT6_441S16_course_notes.pdf>
