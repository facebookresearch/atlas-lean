---
article_id: af_32fafad64fcc12a24b469eba
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.vanAubel
---

# Van Aubel

Van Aubel's theorem (statement `vanaubel-s1` from
    https://en.wikipedia.org/wiki/Van_Aubel%27s_theorem):
    for a quadrilateral with ordered vertices `A`, `B`, `C`, `D`, erect a square
    on each directed side `A → B`, `B → C`, `C → D`, `D → A`; the segments joining
    the centers of opposite squares are equal in length and perpendicular.

Here every square lies to the left of its directed side: its center is the
    side midpoint plus half the side vector rotated counterclockwise by 90 degrees,
    `(x, y) ↦ (-y, x)`. The identity needs no orientation hypothesis. When the
    vertices are listed clockwise these are the outward squares of the source;
    when they are listed counterclockwise they are the inward squares, and
    `vanAubel_right` gives the outward version.
Proves `Wanted` entry `vanAubel`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.VanAubel](../../../../../../sources/v2/MathlibExt.md)
