# The Nussinov recursion

For a complementarity relation and a minimum hairpin size $m$, the Nussinov value $\nu$ of a sequence is defined by recursion on its length: $\nu(\text{empty}) = 0$, and for a sequence $a\,r$ with first letter $a$ and rest $r = r_0 \cdots r_{\ell-1}$,

$$\nu(a\,r) = \max\Bigl(\nu(r),\ \max_{\substack{m \le k < \ell\\ a \text{ complementary to } r_k}} \bigl(1 + \nu(r_0 \cdots r_{k-1}) + \nu(r_{k+1} \cdots r_{\ell-1})\bigr)\Bigr),$$

where a maximum over no index is $0$: the first base is either unpaired, or paired with $r_k$, splitting the rest into the enclosed part and the outer part.
