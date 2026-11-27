# Field lookup

Field lookup in a class table returns, for a class name $C$, either a list of fields (pairs of a class and a field name) or nothing. For $C = \mathtt{Object}$ it returns the empty list (F-OBJECT). Otherwise it walks the [superclass chain](supers.md) of $C$, starting from the empty list: at $\mathtt{Object}$ it keeps the list; at a class $D$ with a declaration it prepends the fields of the first declaration named $D$ (F-CLASS); and at a class with no declaration it fails, and the result is nothing. So the fields of superclasses come first.

Lookup does not detect cycles; the chain is cut off by its length bound. For the one-entry table in which $C \ne \mathtt{Object}$ extends $C$ and declares one field $f$, the chain is $[C, C]$ and lookup returns $f$ twice.
