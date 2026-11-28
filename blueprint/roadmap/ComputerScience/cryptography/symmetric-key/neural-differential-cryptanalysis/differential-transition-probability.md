# Differential transition probability and differential characteristics

For $F:\{0,1\}^n\to\{0,1\}^m$, the probability of the differential $\Delta_{\mathrm{in}}\to\Delta_{\mathrm{out}}$ is the fraction of inputs $x$ with $F(x)\oplus F(x\oplus\Delta_{\mathrm{in}})=\Delta_{\mathrm{out}}$; a characteristic is a sequence of differences through the rounds of an iterated cipher.

Let $n\ge1$, $F:\{0,1\}^n\to\{0,1\}^m$ and $\Delta_{\mathrm{in}}\in\{0,1\}^n$, $\Delta_{\mathrm{out}}\in\{0,1\}^m$. The probability of the differential transition $F:\Delta_{\mathrm{in}}\to\Delta_{\mathrm{out}}$ is

$$
P_F(\Delta_{\mathrm{in}}\to\Delta_{\mathrm{out}})=\frac{\#\{x\in\{0,1\}^n:\ F(x)\oplus F(x\oplus\Delta_{\mathrm{in}})=\Delta_{\mathrm{out}}\}}{2^{n}} ,
$$

the probability over a uniform input $x$. The **difference distribution table** of $F$ lists these probabilities (or counts) for all pairs; it is computed for small components such as S-boxes.

For an iterated cipher with round functions $F_1,\dots,F_r$, a **differential characteristic** is a sequence of differences $\Delta_0,\Delta_1,\dots,\Delta_r$ in which the output difference of each round is the input difference of the next. For a substitution–permutation network, Heys estimates the probability of a characteristic as the product of the probabilities of the difference pairs of its active S-boxes, assuming that the difference pairs in different S-boxes and rounds are independent; this is an estimate, not the exact probability over uniform plaintexts and keys.

## Remarks

Basic facts: $P_F(0\to\Delta_{\mathrm{out}})$ is $1$ if $\Delta_{\mathrm{out}}=0$ and $0$ otherwise; for fixed $\Delta_{\mathrm{in}}$ the probabilities sum to $1$; for $\Delta_{\mathrm{in}}\ne0$ the counts are even, because $x$ and $x\oplus\Delta_{\mathrm{in}}$ are distinct and are counted together. For $F'(x)=F(x\oplus k)$ the transition probabilities do not depend on $k$, since $x\oplus k$ and $x\oplus\Delta\oplus k$ still differ by $\Delta$. Heys states these properties for the difference distribution table of an S-box.

## Depends on

None.

## Proof depends on

None.

## Sources

- Howard M. Heys, "A Tutorial on Linear and Differential Cryptanalysis", Cryptologia 26(3):189–221, 2002, Sections 4.1–4.3 (author copy [https://www.engr.mun.ca/~howard/PAPERS/ldc_tutorial.pdf](https://www.engr.mun.ca/~howard/PAPERS/ldc_tutorial.pdf)).
