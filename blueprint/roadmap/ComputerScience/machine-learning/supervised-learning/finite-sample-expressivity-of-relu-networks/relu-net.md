# Two-layer ReLU network

Let $E$ be a real inner product space. For an input weight vector $a \in E$, biases $b \in \mathbb{R}^m$ and output weights $w \in \mathbb{R}^m$, the two-layer ReLU network computes, for $x \in E$,

$$
c(x) = \sum_{j=1}^m w_j \max\big(\langle a, x\rangle - b_j,\, 0\big).
$$

It is a depth-two network whose $m$ hidden ReLU units share the same input weights $a$ and differ by their biases; on $\mathbb{R}^d$ it has $d + 2m$ weights.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Appendix C, proof of Theorem 1 (the function $c$).
