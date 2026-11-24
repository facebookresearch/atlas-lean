# Merge Trace Primitives

## Call-site provenance

- [Merge Memcpy Site](merge-memcpy-site.md)
- [Backings](backings.md)
- [Distinct](distinct.md)
- [Main To Temp Permit](main-to-temp-permit.md)
- [Temp To Main Permit](temp-to-main-permit.md)

## Signed temporary ranges and backward cursors

- [Temp Index In Bounds](temp-index-in-bounds.md)
- [Temp Range In Bounds](temp-range-in-bounds.md)
- [Backward Cursor In Range](backward-cursor-in-range.md)
- [Temp Range Initialized](temp-range-initialized.md)
- [Temp Range Values Mode](temp-range-values-mode.md)

## Explicit untraced cores

- [Merge Temp Read?](merge-temp-read.md)
- [Merge Temp Write?](merge-temp-write.md)
- [Main To Temp Cell?](main-to-temp-cell.md)
- [Temp To Main Cell?](temp-to-main-cell.md)
- [Main To Temp Memcpy?](main-to-temp-memcpy.md)
- [Temp To Main Memcpy?](temp-to-main-memcpy.md)
- [Main Data Memmove?](main-data-memmove.md)

## Typed one-cell phases

- [Main To Temp Key Traced?](main-to-temp-key-traced.md)
- [Main To Temp Values Traced?](main-to-temp-values-traced.md)
- [Main To Temp Cell Traced?](main-to-temp-cell-traced.md)
- [Temp To Main Key Traced?](temp-to-main-key-traced.md)
- [Temp To Main Values Traced?](temp-to-main-values-traced.md)
- [Temp To Main Cell Traced?](temp-to-main-cell-traced.md)

## Recursively tagged bulk phases

- [Main To Temp Keys Traced?](main-to-temp-keys-traced.md)
- [Main To Temp Values Phase Traced?](main-to-temp-values-phase-traced.md)
- [Main To Temp Memcpy Traced?](main-to-temp-memcpy-traced.md)
- [Temp To Main Keys Traced?](temp-to-main-keys-traced.md)
- [Temp To Main Values Phase Traced?](temp-to-main-values-phase-traced.md)
- [Temp To Main Memcpy Traced?](temp-to-main-memcpy-traced.md)
- [Main Data Memmove Traced?](main-data-memmove-traced.md)

## Structural frame

- [Merge Movement Frame](merge-movement-frame.md)
- [Temp Storage Inv](temp-storage-inv.md)
- [Live](live.md)

## Absence of control-flow events

- [Movement Access Only](movement-access-only.md)

## Common trace safety

- [Has Access](has-access.md)
- [Has Temp Access](has-temp-access.md)
- [Movement Trace Safe](movement-trace-safe.md)
- [Record Success Memory Event](record-success-memory-event.md)

## One-cell totality and complete trace safety

- [Main To Temp Cell eq some of bounds](main-to-temp-cell-eq-some-of-bounds.md)
- [Temp To Main Cell eq some of bounds](temp-to-main-cell-eq-some-of-bounds.md)
- [Main To Temp Cell Traced safe](main-to-temp-cell-traced-safe.md)
- [Temp To Main Cell Traced safe](temp-to-main-cell-traced-safe.md)

## Bulk phase totality and trace safety

- [Main To Temp Memcpy Traced safe](main-to-temp-memcpy-traced-safe.md)
- [Temp To Main Memcpy Traced safe](temp-to-main-memcpy-traced-safe.md)

## Bulk initialization and values-mode preservation

- [Main To Temp Memcpy read before of eq some](main-to-temp-memcpy-read-before-of-eq-so.md)
- [Main To Temp Memcpy values Mode of eq some](main-to-temp-memcpy-values-mode-of-eq-so.md)
- [Temp To Main Memcpy temp eq of eq some](temp-to-main-memcpy-temp-eq-of-eq-some.md)
- [Temp To Main Memcpy values Mode of eq some](temp-to-main-memcpy-values-mode-of-eq-so.md)

## Non-vacuous event witnesses

- [Main To Temp Memcpy Traced events](main-to-temp-memcpy-traced-events.md)
- [Temp To Main Memcpy Traced events](temp-to-main-memcpy-traced-events.md)

## Main-data one-cell decrement copy

- [Main Data Copy Decr Traced?](main-data-copy-decr-traced.md)
- [Main Data Copy Decr Traced safe](main-data-copy-decr-traced-safe.md)
- [Main Data Memmove Traced safe](main-data-memmove-traced-safe.md)
