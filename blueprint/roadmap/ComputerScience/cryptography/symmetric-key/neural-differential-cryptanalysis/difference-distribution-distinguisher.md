# Difference-distribution distinguisher

In the distinct-pair real-versus-random model, a pair with ciphertext difference $\delta$ is classified real when the predicted probability $p(\delta)$ that a real pair has difference $\delta$ exceeds $1/(2^b-1)$, the probability of $\delta$ under random pairs. With the exact law $p$ this is the best rule that sees only $\delta$.

Fix an $r$-round cipher with block size $b$, a nonzero input difference $\Delta$, and the distinct-pair real-versus-random experiment with equal priors. Let $p(\delta)$ be a predicted probability that a real pair has output difference $\delta=C_0\oplus C_1$. The **difference-distribution distinguisher** classifies a pair as real iff

$$
p(\delta)>\frac{1}{2^{b}-1}.
$$

Under random pairs $\delta$ is uniform on the $2^b-1$ nonzero blocks, so if $p$ is the exact law of $\delta$ for real pairs, this rule maximises accuracy among rules that depend only on $\delta$ (ties at equality are assigned to "random"; any assignment is optimal). Gohr takes $p$ to be the Markov-model prediction for Speck32/64 with $\Delta=\mathtt{0x0040/0000}$, computed for up to eight rounds by iterating the one-round transition matrix; the optimality statement does not transfer to that approximation, and his reported accuracies for this rule are computed under the assumption that the prediction is exact, with true positive rates checked empirically.

## Expansion

Optimality is Bayes' rule with equal priors: choose the label whose likelihood of $\delta$ is larger. A different classifier uses the whole pair. With uniform key and plaintext, $\Pr[C\mid\text{real}]=N(C)/2^{b+k}$ where $N(C)$ is the number of keys under which $(C_0,C_1)$ decrypts to a plaintext pair with difference $\Delta$, and in the distinct-pair model $\Pr[C\mid\text{random}]=1/(2^{2b}-2^b)$; the Bayes rule is "real" iff $N(C)>2^{b+k}/(2^{2b}-2^b)$. For Speck32/64 Gohr implements the comparison with the cutoff $2^{32}$ and reports about 95% accuracy on $10^4$ five-round test pairs.

## Depends on

- [Real-versus-random experiments for differential distinguishers](real-versus-random-differential-experiment.md)
- [Differential transition probability and differential characteristics](differential-transition-probability.md)

## Proof depends on

None.

## Sources

- Aron Gohr, "Improving Attacks on Round-Reduced Speck32/64 Using Deep Learning", CRYPTO 2019, Lecture Notes in Computer Science 11693, pp. 150–179, https://doi.org/10.1007/978-3-030-26951-7_6; numbers from IACR ePrint 2019/037, [https://eprint.iacr.org/2019/037](https://eprint.iacr.org/2019/037), Section 3.1 (classification, sources of error) and Section 3.2 (key-counting distinguisher for five rounds), Table 2.
