# First-class continuations with callcc and abort: type safety

## Structural properties of typing

- [Renaming preserves typing](rename.md)
- [Weakening](weaken.md)
- [Parallel substitution preserves typing](subst.md)
- [Substitution lemma](instantiate.md)

## Evaluation contexts

- [Renaming commutes with plugging](rename-plug.md)
- [Typing of a plugged context, inverted](plug-inv.md)
- [Typing of a plugged context](plug.md)
- [Renaming preserves the typing of contexts](rename-2.md)
- [Typing of the continuation of a context](reify.md)

## Progress and preservation

- [Progress](progress.md)
- [Preservation for programs](preservation.md)

## Safety through the schema

- [Typed programs reach only values or reducible programs](final-or-step.md)
- [Typed programs never get stuck](not-stuck.md)
- [The calculus with callcc has the structural properties](structural-typing.md)

## Peirce's law and abort-free programs

- [Callcc has the type of Peirce's law](peirce.md)
- [The answer type is irrelevant without abort](answer-irrelevant.md)
- [Abort-free programs never get stuck](final-or-step-abort-free.md)
