# Index construction and postings compression

This node collects correctness of inverted-index construction and of the standard postings-list
compression codes.

## Expansion

A sound expansion has separate pages for:

1. **Construction.** Sort-based (BSBI), single-pass in-memory (SPIMI) and multiway-merge construction all
   produce the inverted index of the definition.
2. **Gap transform.** For a strictly increasing list of positive document identifiers, the gaps (the first
   identifier, then successive differences, all positive) determine the list by prefix sums.
3. **Prefix codes.** Variable-byte, Elias gamma and Golomb–Rice codes with parameter $b \ge 1$ are prefix-free
   on positive integers, so concatenations decode uniquely; the gamma code of $x \ge 1$ has
   $2\lfloor \log_2 x \rfloor + 1$ bits.
4. **Optimality.** For the geometric distribution $\Pr(x) = (1-p)^{x-1} p$ on $x \ge 1$, with $0 < p < 1$,
   the Golomb code with parameter $b = \lceil \log(2-p) / (-\log(1-p)) \rceil$ has the least expected codeword
   length among all prefix codes on the positive integers (Gallager and Van Voorhis); other parameters need
   not.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Inverted index and postings-merge correctness.

## Depends on

- [Prefix-free code](../../../InformationTheory/source-coding/prefix-codes/is-prefix-free.md)

## Sources

- Inverted Files for Text Search Engines (Zobel, Moffat), ACM Computing Surveys 2006 — ACM Computing Surveys 38(2) 2006, Section 5 (index construction) and Section 8 (efficient index representations, pp. 19–21: d-gaps, unary, Elias gamma and delta, bytewise, Golomb and Rice codes, and the minimum-redundancy parameter for geometric distributions, credited to Gallager and Van Voorhis). <http://people.eng.unimelb.edu.au/jzobel/fulltext/compsurv06.pdf>
- Introduction to Information Retrieval (Manning, Raghavan, Schutze) — Cambridge University Press 2008; authors' online edition, Section 4.2 (blocked sort-based indexing and merging of blocks), Section 4.3 (single-pass in-memory indexing), Section 5.3 (variable byte codes, and γ codes of $2\lfloor \log_2 G \rfloor + 1$ bits, which are prefix free). <https://nlp.stanford.edu/IR-book/pdf/irbookonlinereading.pdf>
