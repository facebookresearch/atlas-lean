# Polar transform: channel combining/splitting conservation

Let $W$ be a binary-input discrete memoryless channel with a finite output alphabet and let $I(W)$ be its symmetric
capacity, the mutual information in bits with a uniform input. Combining two independent copies by $(u_1, u_2) \mapsto (u_1 \oplus u_2, u_2)$ with independent uniform bits $u_1, u_2$,
the synthetic channels $W^- : u_1 \to (y_1, y_2)$ and $W^+ : u_2 \to (y_1, y_2, u_1)$ satisfy
$I(W^-) + I(W^+) = 2 I(W)$ and $I(W^-) \le I(W) \le I(W^+)$. Recursive application on $N = 2^n$ copies defines the synthetic
channels whose polarization is Arıkan's theorem, a separate page.

## Depends on

- [Mutual information of a finite joint law](../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Related topics

- [Weak converse for discrete memoryless channels](shannon-s-channel-coding-theorem/channel-coding-weak-converse.md)

## Sources

- E. Arıkan, Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input
  memoryless channels, IEEE Trans. Inform. Theory 55(7) (2009), arXiv:0807.3917v3: Section I-B (symmetric capacity) and
  Proposition 5, (25) and (26), for the single-step transform $(W, W) \mapsto (W', W'')$. <https://arxiv.org/abs/0807.3917v3>
