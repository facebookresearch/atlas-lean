# Two-user discrete memoryless multiple-access channel and its capacity region

A two-user discrete memoryless multiple-access channel is a stochastic map $W(y \mid a, b)$ from finite input
alphabets $\mathcal{A} \times \mathcal{B}$ to a finite output alphabet $\mathcal{Y}$, used memorylessly. An
$(n, M_1, M_2, \varepsilon)$ code consists of encoders $f_1 : [M_1] \to \mathcal{A}^n$, $f_2 : [M_2] \to \mathcal{B}^n$ and
a decoder $g : \mathcal{Y}^n \to [M_1] \times [M_2]$ whose average error probability, for independent uniform messages,
is at most $\varepsilon$. Let $R^*_n(\varepsilon)$ be the set of rate pairs $(R_1, R_2)$ with $R_1, R_2 \ge 0$ for
which an $(n, M_1, M_2, \varepsilon)$ code with $M_1 \ge 2^{nR_1}$ and $M_2 \ge 2^{nR_2}$ exists; this set is downward
closed. The capacity region is

$$\mathcal{C} = \bigcap_{\varepsilon > 0} \overline{\liminf_{n \to \infty} R^*_n(\varepsilon)},$$

where the set limit inferior consists of the rate pairs that belong to $R^*_n(\varepsilon)$ for all sufficiently
large $n$.

## Sources

- Y. Polyanskiy and Y. Wu, *Lecture notes on information theory*, MIT 6.441, Spring 2016, Definition 26.1. <https://ocw.mit.edu/courses/6-441-information-theory-spring-2016/5d8f16adc3385c9ff2975b121bd620e4_MIT6_441S16_course_notes.pdf>
