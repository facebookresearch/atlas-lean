# Named and positional relational carriers

This node collects the correspondence between the named and positional (unnamed) perspectives on
relational tuples and queries.

## Expansion

A sound expansion has separate pages for:

1. **Tuple transport.** Fix a duplicate-free enumeration of each finite attribute schema; tuples defined
   exactly on that schema correspond bijectively to positional tuples of its arity, and the correspondence
   commutes with projection, renaming and join as stated on the page.
2. **Answer transport.** For a safe conjunctive query with constants over a nonempty domain $D$ and an
   instance over $D$, an injective encoding into the natural numbers of the values of the instance and of
   the query constants, applied also to the constants of the query, maps the answer set over $D$ onto the
   answer set of the encoded query on the encoded instance.
3. **Containment transport.** For safe, arity-checked conjunctive queries with constants over an infinite
   domain $D$ and an injective encoding of their constants into the natural numbers, one query is
   contained in the other over $D$ if and only if the encoded queries are contained over the natural
   numbers.

No bijection between $D$ and the natural numbers is assumed. The empty domain, finite domains in item 3
and unsafe queries are outside these statements and need their own conventions.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Depends on

- [Tuple](../relational-algebra/tuple.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Section 3.2 (named versus unnamed perspectives, pp. 31–32). <http://webdam.inria.fr/Alice/pdfs/all.pdf>
