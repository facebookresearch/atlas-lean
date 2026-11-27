# HMAC

## Structural lemmas: a leading full block

- [Padding behind a prefix](pad-tail.md)
- [Padding a concatenation](pad-append.md)
- [Splitting off a leading block](blocks-append.md)
- [Moving the first block into the chaining value](hash-cons.md)
- [Continuation hash](cont-hash.md)
- [Hashing a one-block prefix](full-hash-vector-append.md)

## The construction

- [Bitwise exclusive or of two words](xor-block.md)
- [HMAC](hmac.md)
- [Derived inner and outer keys](inner-key.md)
- [Nested continuation hash](nested-cont-hash.md)
- [HMAC in nested form](hmac-eq-nested-cont-hash.md)
- [HMAC depends on the key only through the derived keys](hmac-eq-of-inner-key-eq.md)

## HMAC as a MAC

- [HMAC as a MAC on encoded messages](hmac-scheme-on.md)
- [Hmac Scheme](hmac-scheme.md)
- [Correctness of HMAC on encoded messages](hmac-scheme-on-correct.md)
- [Correctness](hmac-scheme-correct.md)

## The Framework forgery experiment of HMAC

- [HMAC forgery experiment for forgers with arbitrary coins](mac-game-hmac-scheme-on.md)
- [Forgery bound for HMAC on finite encoded messages](hmac-scheme-on-mac-advantage-le.md)
- [HMAC forgery experiment for forgers with uniform coins](mac-game-hmac-scheme-on-of-uniform.md)
- [Forgery bound for HMAC against forgers with uniform coins](hmac-scheme-on-mac-advantage-le-of-unifo.md)

## Forgers against `hmacScheme` with length-bounded messages

- [HMAC forgery is invariant under injective message encodings](mac-game-hmac-scheme-relabel.md)
- [Forgery bound for HMAC on length-bounded bit strings](hmac-scheme-mac-advantage-le.md)
