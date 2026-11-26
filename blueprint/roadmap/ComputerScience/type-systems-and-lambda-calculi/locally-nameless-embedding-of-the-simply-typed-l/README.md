# Locally nameless embedding of the simply typed lambda calculus

## Stlc

- [Locally nameless lambda terms with natural-number names](locally-nameless-term.md)
- [Locally nameless typing contexts with natural-number names](locally-nameless-context.md)

## Raw Tm

- [Translation of raw de Bruijn terms to locally nameless terms](to-locally-nameless-aux.md)
- [Opening a translated term at the next binder extends the name list](open-to-locally-nameless-aux.md)
- [Translating a shifted raw term cancels the shift](to-locally-nameless-aux-shift.md)
- [Raw beta substitution at a binder depth](beta-sub.md)
- [Lifting a raw beta substitution increments its depth](lift-sub-beta-sub.md)
- [Translating a raw beta substitution is locally nameless opening](to-locally-nameless-aux-beta-sub.md)
- [Raw beta substitution at depth zero is single-variable substitution](beta-sub-zero.md)

## Stlc

- [Locally nameless context from a list of names and a simply typed context](locally-nameless-context-with.md)
- [Names of the paired locally nameless context](locally-nameless-context-with-keys.md)
- [Distinct names give a well-formed locally nameless context](locally-nameless-context-with-well-forme.md)

## Var

- [The de Bruijn index of a typed variable is below the context length](to-nat-lt-length.md)
- [A source variable lies in the paired locally nameless context](mem-locally-nameless-context-with.md)

## Tm

- [Locally nameless embedding of intrinsic terms with chosen names](to-locally-nameless-with.md)
- [Opening a translated lambda body prepends a fresh name](open-to-locally-nameless-with-lam.md)
- [Instantiation embeds as locally nameless opening](to-locally-nameless-with-instantiate.md)
- [The locally nameless embedding with distinct names preserves typing](to-locally-nameless-with-typing.md)
- [Canonical locally nameless context of a simply typed context](locally-nameless-context-2.md)
- [Canonical locally nameless embedding of intrinsic terms](to-locally-nameless.md)
- [The canonical locally nameless embedding preserves typing](to-locally-nameless-typing.md)
- [Canonical locally nameless embeddings are locally closed](to-locally-nameless-lc.md)
