# Differential transition probability and differential characteristics

For $F:\{0,1\}^n\to\{0,1\}^m$, the probability of the differential $\Delta_{\mathrm{in}}\to\Delta_{\mathrm{out}}$ is the fraction of inputs $x$ with $F(x)\oplus F(x\oplus\Delta_{\mathrm{in}})=\Delta_{\mathrm{out}}$; a characteristic is a sequence of differences through the rounds of an iterated cipher.

Let $n\ge1$, $F:\{0,1\}^n\to\{0,1\}^m$ and $\Delta_{\mathrm{in}}\in\{0,1\}^n$, $\Delta_{\mathrm{out}}\in\{0,1\}^m$. The probability of the differential transition $F:\Delta_{\mathrm{in}}\to\Delta_{\mathrm{out}}$ is

$$
P_F(\Delta_{\mathrm{in}}\to\Delta_{\mathrm{out}})=\frac{\#\{x\in\{0,1\}^n:\ F(x)\oplus F(x\oplus\Delta_{\mathrm{in}})=\Delta_{\mathrm{out}}\}}{2^{n}} ,
$$

the probability over a uniform input $x$. The **difference distribution table** of $F$ lists these probabilities (or counts) for all pairs; it is computed for small components such as S-boxes.

For an iterated cipher with round functions $F_1,\dots,F_r$, a **differential characteristic** is a sequence of differences $\Delta_0,\Delta_1,\dots,\Delta_r$. A **Markov model** of the cipher assigns to each round the one-round transition probabilities $P_{F_i}(\Delta_{i-1}\to\Delta_i)$, treating the round differences as a Markov chain (in Gohr's words, a Markov cipher is one in which the probability of each differential transition is independent of the concrete plaintext values when the round keys are chosen uniformly at random); in that model the probability of the characteristic is $\prod_{i=1}^{r}P_{F_i}(\Delta_{i-1}\to\Delta_i)$, and the probability of the differential $\Delta_0\to\Delta_r$ is the sum over characteristics with those endpoints. For an actual cipher these model values approximate the true probabilities over uniform plaintexts and keys; Gohr notes that Speck is not exactly Markov and that the computation is valid only insofar as it does not deviate too strongly.

## Remarks

Basic facts: $P_F(0\to\Delta_{\mathrm{out}})$ is $1$ if $\Delta_{\mathrm{out}}=0$ and $0$ otherwise; for fixed $\Delta_{\mathrm{in}}$ the probabilities sum to $1$; for $\Delta_{\mathrm{in}}\ne0$ the counts are even, because $x$ and $x\oplus\Delta_{\mathrm{in}}$ are distinct and are counted together. For $F'(x)=F(x\oplus k)$ the transition probabilities do not depend on $k$, since $x\oplus k$ and $x\oplus\Delta\oplus k$ still differ by $\Delta$. Gohr computes the Markov-model output-difference distribution of round-reduced Speck32/64 from one input difference by iterating the one-round transition matrix and checks it against experiment.

## Depends on

None.

## Proof depends on

None.

## Sources

- Aron Gohr, "Improving Attacks on Round-Reduced Speck32/64 Using Deep Learning", CRYPTO 2019, Lecture Notes in Computer Science 11693, pp. 150–179, https://doi.org/10.1007/978-3-030-26951-7_6; numbers from IACR ePrint 2019/037, [https://eprint.iacr.org/2019/037](https://eprint.iacr.org/2019/037), Section 2.1, Equation (1), and Section 3.1 (sources of error).
- Adrien Benamira, David Gerault, Thomas Peyrin, Quan Quan Tan, "A Deeper Look at Machine Learning-Based Cryptanalysis", EUROCRYPT 2021, Lecture Notes in Computer Science 12696, https://doi.org/10.1007/978-3-030-77870-5_28 (conference version, [https://iacr.org/archive/eurocrypt2021/126960385/126960385.pdf](https://iacr.org/archive/eurocrypt2021/126960385/126960385.pdf)), Section 2.2.
- Howard M. Heys, "A Tutorial on Linear and Differential Cryptanalysis", Cryptologia 26(3):189–221, 2002, Section 4 (author copy [https://www.engr.mun.ca/~howard/PAPERS/ldc_tutorial.pdf](https://www.engr.mun.ca/~howard/PAPERS/ldc_tutorial.pdf)).
