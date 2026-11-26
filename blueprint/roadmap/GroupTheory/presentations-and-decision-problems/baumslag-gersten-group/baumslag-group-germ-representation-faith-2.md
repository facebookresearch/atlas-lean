# Baumslag's germ representation is not faithful

Let $B$ be Baumslag's group
$\langle a, b \mid (bab^{-1})\, a\, (bab^{-1})^{-1} = a^2 \rangle$, let $f(x) = 2x$ and
$g(x) = 2^x$, and for $w$ in the free group on $a, b$ with reduced word $l_1 l_2 \cdots l_k$ let
$\varphi_w = \varphi_{l_1} \circ \varphi_{l_2} \circ \cdots \circ \varphi_{l_k}$, where
$\varphi_a = f$, $\varphi_{a^{-1}}(x) = x/2$, $\varphi_b = g$ and $\varphi_{b^{-1}}(x) = \log_2 x$.
The representation $a \mapsto f$, $b \mapsto g$ of $B$ by germs at $+\infty$ is not faithful: there
is an element $w$ of the free group on $a, b$ such that $\varphi_w(x) = x$ for all sufficiently
large real $x$, but the image of $w$ in $B$ is not trivial.

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.99 (A. Yu. Olshanskii); resolution: C.-F. Nyberg-Brodda, The Baumslag-Gersten group and a problem of Olshanskii, preprint, arXiv:2606.27408 (2026), abstract (the representation of BG(1, 2) by germs is not faithful: an explicit non-trivial element of its kernel); the Kourovka Notebook (21st issue) marks 17.99 solved (No, it is not), https://arxiv.org/abs/2606.27408.
