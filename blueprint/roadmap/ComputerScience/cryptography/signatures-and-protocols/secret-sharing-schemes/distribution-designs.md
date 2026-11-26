# Distribution designs and random-less composition of secret sharing

A *distribution design* from an access structure $\mathcal{A}'$ on $n'$ virtual parties to $\mathcal{A}$ on $n$ real parties assigns to each real party a set of virtual parties such that $S \in \mathcal{A}$ iff the union of the assigned sets is in $\mathcal{A}'$, i.e. $\mathcal{A}$ is the pullback of $\mathcal{A}'$. Composing a scheme for $\mathcal{A}'$ with a design, giving each real party the tuple of shares of its virtual parties, yields a scheme for $\mathcal{A}$ with the same key distributions and no additional randomness; perfect correctness, perfect privacy and $\delta$-statistical privacy are all preserved.

## Proof sketch

The view of a real coalition is a deterministic relabelling of the view of the corresponding virtual coalition, which is authorized exactly when the real coalition is.

## Depends on

- [Monotone access structures and secret-sharing schemes](access-structures-and-secret-sharing.md)

## Sources

- Divesh Aggarwal, "Secret Sharing Despite Non-Extractable Randomness", arXiv:2610.20173v2, 2026.
