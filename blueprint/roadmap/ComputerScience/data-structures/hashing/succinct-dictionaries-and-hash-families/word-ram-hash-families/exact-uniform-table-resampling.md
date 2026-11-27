# Exact uniform resampling of random tables on the Word RAM

On a Word RAM whose `rand` instruction returns a uniform word below a given bound, a loop that fills $N$ table entries with independent `rand` draws below $2^M$ ($M \le w$) produces, as the distribution of the table contents, exactly the uniform distribution on $[2^M]^N$; when the entries are $b$-bit fields packed in words, filling the packed array word by word with `rand` draws below $2^w$ gives the uniform distribution on $[2^b]^N$. The loop runs in $O(N)$ instructions.

## Proof sketch

The loop's output is a product of independent uniform draws, one per entry, and reading the fields of a packed array selects disjoint sets of bit positions of uniformly random words, so the fields are independent and uniform (bits outside every field are ignored).

## Depends on

- [Word-RAM resamplable hash family](word-ram-resamplable-hash-family.md)
- [Bit-packed array on the Word RAM](bit-packed-array.md)

## Sources

- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
