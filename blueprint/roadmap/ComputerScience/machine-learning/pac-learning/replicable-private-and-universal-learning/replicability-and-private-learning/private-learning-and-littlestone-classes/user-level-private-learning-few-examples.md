# User-level private learning from item-level private learning with few examples per user

In **user-level** differential privacy the dataset consists of $n$ users each contributing $m$ examples, and neighbouring datasets may differ in all examples of one user. For approximate differential privacy there is a generic transformation turning any item-level private algorithm into a user-level private algorithm whose number of users needed for the same utility is smaller by a multiplicative factor $O_{\varepsilon,\delta}(\sqrt{m})$, even when each user holds few examples. For pure differential privacy, an adaptation of the exponential mechanism to the user level gives new bounds for private PAC learning, hypothesis selection and distribution learning, which are near-optimal for some of these tasks.

## Proof sketch

The approximate-privacy transformation runs the item-level algorithm on many random pseudo-datasets assembled from user contributions and privately aggregates outputs through a stability argument: when users hold $m$ examples, the effect of replacing one user is spread over $m$ items whose combined influence on a stable algorithm scales like $\sqrt{m}$ rather than $m$ by concentration. The pure-privacy result scores candidate outputs by the number of users whose data is well explained and applies the exponential mechanism with user-level sensitivity one.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)

## Proof depends on

- [The exponential mechanism is differentially private](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)

## Sources

- B. Ghazi, P. Kamath, R. Kumar, P. Manurangsi, R. Meka, C. Zhang, "User-Level Differential Privacy With Few Examples Per User", NeurIPS (2023), arXiv:2309.12500, abstract and Section 1.
- M. Bun, M. Gaboardi, M. Hopkins, R. Impagliazzo, R. Lei, T. Pitassi, S. Sivakumar, J. Sorrell, "Stability is Stable: Connections between Replicability, Privacy, and Adaptive Generalization", STOC (2023), arXiv:2303.12921.
